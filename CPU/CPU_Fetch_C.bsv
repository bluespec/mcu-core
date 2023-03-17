// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

package CPU_Fetch_C;

// ================================================================
// mkCPU_Fetch_C is an IMem_IFC->Module#(IMem_IFC) wrapper.

// The input parameter interface is for 32-bit-aligned 32-bit instruction-fetches.

// This module completely encapsulates the logic needed to extend it to
// 16-bit "compressed" instructions ('C' extension)
// which then also includes 32-bit instructions which may be only 16-bit-aligned,
// since 32b and 16b instructions can be freely mixed.

// ----------------------------
// Compressed Instruction Fetch
// ----------------------------
//


// ================================================================
// BSV lib imports

import GetPut       :: *;
import ClientServer :: *;

// ----------------
// BSV additional libs

import Cur_Cycle :: *;

// ================================================================
// Project imports

import ISA_Decls    :: *;
import Near_Mem_IFC :: *;

// ================================================================
// Functions concerning address-alignment of instructions.
// 'Even': aligned to an even 16b boundary (so, also aligned to 32b boundary)
// 'Odd':  aligned to an odd  16b boundary (so, not  aligned to 32b boundary)

function Bool is_addr_even16 (WordXL pc);
   return (pc [1:0] == 2'b00);
endfunction

function Bool is_addr_odd16 (WordXL pc);
   return (pc [1:0] != 2'b00);
endfunction

function WordXL fn_to_b32_addr (WordXL addr);
   return ((addr >> 2) << 2);
endfunction

// Equality of 32-bit aligned addresses containing a1 and a2 (i.e., ignoring [1:0])
function Bool eq_b32_addr (WordXL a1, WordXL a2) = ((a1 >> 2) == (a2 >> 2));

// ================================================================
// Functions concerning whether an instr is 32b (RV) or 16b (RVC)

function Bool is_32b_instr (Bit #(n) instr);
   return (instr [1:0] == 2'b11);
endfunction

function Bool is_16b_instr (Bit #(n) instr);
   return (instr [1:0] != 2'b11);
endfunction

typedef enum {IDLE, NEW_RSP, I32_ODD_RSP} CFetchFSM
deriving (Bits, Eq, FShow);

interface CPU_Fetch_C_IFC;
   interface IMem_IFC imem;
   method Action reset;
endinterface

// ================================================================
// Wrapper: wraps 32-bit aligned IMem to allow 16-bit instrs and 32-bit instrs,
// aligned to 16b or 32b boundaries.

module mkCPU_Fetch_C #(IMem_IFC  imem32) (CPU_Fetch_C_IFC);

   // imem32 is the underlying 32-bit-aligned memory.
   // imem32.req is only given 32-bit aligned addrs,
   // and returns the 32b at that addr.
   // imem32.pc (output pc) is always the last requested address, always 32b-aligned.
   // ( Assert: imem32.is_32b_not_16b == True )

   // 0: quiet. 1: rule firing. 2: request-response. 3: details
   Integer verbosity = 0;

   // The following hold args of the 'req' method.
   Reg #(WordXL)            rg_pc         <- mkRegU;

   // Exception and instruction outputs
   Reg #(Maybe #(Exc_Code)) rg_exc        <- mkReg (tagged Invalid);
   Reg #(Instr)             rg_instr      <- mkRegU;
   Reg #(Bool)              rg_instr_rdy  <- mkReg (False);

   // State of the compressed fetch FSM
   Reg #(CFetchFSM)         rg_state      <- mkReg (IDLE);

   Wire #(WordXL)           w_addr        <- mkWire;
   // ----------------------------------------------------------------
   // Conditions for selecting 16b and 32b instruction

   // Condition: 32b instr from imem [31:0]
   function Bool fv_cond_i32_even (Instr i);
      return (is_addr_even16 (rg_pc) && is_32b_instr (i));
   endfunction

   // Condition: 32b instr from imem [31:16]
   function Bool fv_cond_i32_odd  (Instr i);
      return (is_addr_odd16 (rg_pc) && is_32b_instr (i [31:16]));
   endfunction

   // Condition: 16b instr from imem [31:16]
   function Bool fv_cond_i16_odd (Instr i); 
      return (is_addr_odd16 (rg_pc) && is_16b_instr (i [31:16]));
   endfunction

   // Condition: 16b instr from imem [15:0]
   function Bool fv_cond_i16_even (Instr i);
      return (is_addr_even16 (rg_pc) && is_16b_instr (i));
   endfunction

   // ================================================================
   // When imem32.instr [31:15] has lower half of 32b instr, cache it and fetch next 32 bits

   rule rl_I32_ODD_RSP (rg_state == I32_ODD_RSP);
      match {.instr, .irsp_exc} <- imem32.instr ();

      // Register the exception which will accompany the instruction
      rg_exc <= irsp_exc;

      // Form the return instruction
      rg_instr_rdy <= True;
      Instr complete_i32 = {instr[15:0], rg_instr[15:0]};
      rg_instr <= complete_i32;

      // Next state logic
      rg_state <= IDLE;

      if (verbosity > 0) begin
	 $display ("%06d:[D]:%m.rl_I32_ODD_RSP: state: ", cur_cycle, fshow (rg_state));
         if (verbosity > 1) begin
            $display ("            irsp_exc     : ", fshow (irsp_exc));
            $display ("            instr        : ", fshow (instr));
         end
      end
   endrule

   rule rl_NEW_RSP (rg_state == NEW_RSP);
      match {.instr, .irsp_exc} <- imem32.instr ();

      // Instruction conditions to form the return instruction
      let cond_i32_even = fv_cond_i32_even (instr);
      let cond_i32_odd  = fv_cond_i32_odd  (instr);
      let cond_i16_even = fv_cond_i16_even (instr);
      let cond_i16_odd  = fv_cond_i16_odd  (instr);

      // Form the return instruction
      let instr_rdy = True;

      // i32 starting from word-aligned address
      if (cond_i32_even)      rg_instr <= instr;

      // i16 starting from word-aligned address
      else if (cond_i16_even) rg_instr <= {16'b0, instr[15:0]};

      // i16 starting from hword-aligned address
      else if (cond_i16_odd)  rg_instr <= {16'b0, instr[31:16]};

      // i32 starting from hword-aligned address
      // The required instruction straddles the word boundary: launch the
      // subsequent imem read and wait for its response to complete fetch
      else begin
         instr_rdy = False; rg_instr <= {16'b0, instr[31:16]};
         WordXL addr_of_nxt_b32 = (fn_to_b32_addr (rg_pc) + 4);
         imem32.req (addr_of_nxt_b32);
      end

      // Indicate instruction is ready in all cases except i32_odd
      rg_instr_rdy <= instr_rdy;

      // Register the exception which will accompany the instruction
      rg_exc <= irsp_exc;

      // Return to IDLE except when fetching i32_odd
      rg_state <= cond_i32_odd ? I32_ODD_RSP : IDLE;

      if (verbosity > 0) begin
	 $display ("%06d:[D]:%m.rl_NEW_RSP: state: ", cur_cycle, fshow (rg_state));
         if (verbosity > 1) begin
            $display ("            irsp_exc     : ", fshow (irsp_exc));
            $display ("            instr_rdy    : ", fshow (instr_rdy));
            $display ("            instr        : ", fshow (instr));

            if (verbosity > 2) begin
               $display ("            cond_i32_even: ", fshow (cond_i32_even));
               $display ("            cond_i32_odd : ", fshow (cond_i32_odd));
               $display ("            cond_i16_even: ", fshow (cond_i16_even));
               $display ("            cond_i16_odd : ", fshow (cond_i16_odd));
            end
         end
      end
   endrule

   rule rl_new_req (rg_state == IDLE);
      let addr = w_addr;

      // What is the word-aligned address of the request
      WordXL addr_of_b32 = fn_to_b32_addr (addr);

      // Launch the new fetch
      imem32.req (addr_of_b32);

      // Remember the requested address as PC
      rg_pc <= addr;

      // Update fetch state machine
      rg_state <= NEW_RSP;

      if (verbosity > 0) begin
         $display ("%06d:[D]:%m.rl_new_req: state: ", cur_cycle, fshow (rg_state));
         if (verbosity > 1) begin
            $display ("            (addr 0x%08h), (addr_of_b32 0x%08h)", addr, addr_of_b32, rg_pc);
         end
      end
   endrule

   // ================================================================
   // INTERFACE

   method Action reset;
      if (verbosity > 1) $display ("%06d: [D]: %m.reset", cur_cycle);
      rg_exc <= tagged Invalid;
      rg_instr_rdy <= False;
      rg_state <= IDLE;
   endmethod

   interface IMem_IFC imem;
      // CPU side: IMem request. Actions moved to a separate rule
      // to mention in scheduling pragmas in mkCPU
      method Action req (WordXL addr) if (rg_state == IDLE);
         w_addr <= addr;
      endmethod

      // CPU side: IMem response
      method ActionValue #(Tuple2 #(Instr, Maybe #(Exc_Code))) instr if (rg_instr_rdy);
         rg_instr_rdy <= False;
         return (tuple2 (rg_instr, rg_exc));
      endmethod
   endinterface
endmodule

// ================================================================

endpackage
