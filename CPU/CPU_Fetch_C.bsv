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

typedef enum {IDLE, VALID_B16, NEW_RSP, I32_ODD_RSP, I16_ODD_RSP} CFetchFSM
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

   Integer verbosity = 0;

   // The following hold args of the 'req' method.
   Reg #(WordXL)            rg_pc         <- mkRegU;

   // Exception and instruction outputs
   Reg #(Maybe #(Exc_Code)) rg_exc        <- mkReg (tagged Invalid);
   Reg #(Maybe #(Instr))    rg_instr      <- mkReg (tagged Invalid);

   // Caches the last output of imem32 (imem32.instr [31:16])
   Reg #(Bit #(16))         rg_cache_b16  <- mkRegU;

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
      rg_instr <= tagged Valid ({instr[15:0], rg_cache_b16});

      // Remember the upper half-word of the imem response. Whether we use it
      // or not depends on future fetch addresses
      rg_cache_b16 <= instr[31:16];

      // Next state logic
      rg_state <= VALID_B16;

      if (verbosity > 0) begin
	 $display ("%06d:[D]:%m.rl_I32_ODD_RSP: state: ", cur_cycle, fshow (rg_state));
         if (verbosity > 1) begin
            $display ("            irsp_exc     : ", fshow (irsp_exc));
            $display ("            irsp_instr   : ", fshow (instr));
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
      if (cond_i32_even)      rg_instr <= tagged Valid (instr);
      else if (cond_i16_even) rg_instr <= tagged Valid ({16'b0, instr[15:0]});
      else if (cond_i16_odd)  rg_instr <= tagged Valid ({16'b0, instr[31:16]});
      else                    rg_instr <= tagged Invalid;

      // Register the exception which will accompany the instruction
      rg_exc <= irsp_exc;

      // Remember the upper half-word of the imem response. Whether we use it
      // or not depends on the next state.
      rg_cache_b16 <= instr[31:16];

      // Next state logic
      // The next state will indicate that there is a valid upper half-word
      // cached, unless ...
      let nstate = VALID_B16;

      // The required instruction straddles the word boundary: launch the
      // subsequent imem read and wait for its response to complete fetch
      if (cond_i32_odd) begin
         nstate = I32_ODD_RSP;
         WordXL addr_of_nxt_b32 = (fn_to_b32_addr (rg_pc) + 4);
         imem32.req (addr_of_nxt_b32);
      end

      // Using up the complete instruction or the upper half-word
      // Discard the unused part as it is behind the current fetch
      else if ((cond_i32_even) || (cond_i16_odd))
         nstate = IDLE;

      rg_state <= nstate;

      if (verbosity > 0) begin
	 $display ("%06d:[D]:%m.rl_NEW_RSP: state: ", cur_cycle, fshow (rg_state));
         if (verbosity > 1) begin
            $display ("            cond_i32_even: ", fshow (cond_i32_even));
            $display ("            cond_i32_odd : ", fshow (cond_i32_odd));
            $display ("            cond_i16_even: ", fshow (cond_i16_even));
            $display ("            cond_i16_odd : ", fshow (cond_i16_odd));
            $display ("            irsp_exc     : ", fshow (irsp_exc));
            $display ("            irsp_instr   : ", fshow (instr));
         end
      end
   endrule

   // When imem32.instr [31:15] is the next i16 instruction 
   rule rl_I16_ODD_RSP (rg_state == I16_ODD_RSP);
      rg_instr <= tagged Valid ({16'b0, rg_cache_b16});
      rg_exc   <= tagged Invalid;
      rg_state <= IDLE;
      if (verbosity > 0)
	 $display ("%06d:[D]:%m.rl_I16_ODD_RSP: state: ", cur_cycle, fshow (rg_state));
   endrule

   rule rl_new_req ((rg_state == IDLE) || (rg_state == VALID_B16));
      let addr = w_addr;

      // What is the word-aligned address
      WordXL addr_of_b32 = fn_to_b32_addr (addr);
      let nstate         = IDLE;
      Bool new_request   = False;

      // A new request when there is no remnants of an older instruction
      if (rg_state == IDLE) begin
         new_request = True;
         nstate = NEW_RSP;
      end

      // A valid remnant of a former fetch exists (rg_state == VALID_B16)
      else begin
         if (addr == rg_pc) begin
            // the new fetch address is same as the just fetched
            // PC. This can happen in a BREAK or on a self-loop.
            // Treat it like a new request.
            new_request = True;
            nstate = NEW_RSP;
         end

         // The word address of the new request is same as of the remnant
         else if (eq_b32_addr (addr, rg_pc)) begin
            // A 32-bit instruction starting from the halfword
            // boundary. Launch a fetch of the missing piece which
            // is in the next b32 chunk
            if (is_32b_instr (rg_cache_b16)) begin
               new_request = True;
               addr_of_b32 = addr_of_b32 + 4;
               nstate = I32_ODD_RSP;
            end

            // A 16-bit instruction starting from a halfword boundary
            // The instruction is already available. 
            // We could have responded right away but that introduces a long
            // path from rl_exec2.  Introducing a new state to break the path.
            else nstate = I16_ODD_RSP;
         end

         // The address of the new request is not the same as of the remnant
         // This is like a new fetch.
         else begin
            new_request = True;
            nstate = NEW_RSP;
         end
      end

      // Launch the new fetch
      if (new_request) imem32.req (addr_of_b32);

      // Remember the PC
      rg_pc <= addr;

      // Update fetch state machine
      rg_state <= nstate;

      if (verbosity > 0) begin
	 $display ("%06d:[D]:%m.rl_new_req: state: ", cur_cycle, fshow (rg_state));
         if (verbosity > 1) begin
            $display ("            (addr 0x%08h), (addr_of_b32 0x%08h) (rg_pc 0x%08h)", addr, addr_of_b32, rg_pc);
         end
      end
   endrule

   // ================================================================
   // INTERFACE

   method Action reset;
      if (verbosity > 1) $display ("%06d: [D]: %m.reset", cur_cycle);
      rg_exc <= tagged Invalid;
      rg_instr <= tagged Invalid;
      rg_state <= IDLE;
   endmethod

   interface IMem_IFC imem;
      // CPU side: IMem request
      method Action req (WordXL addr) if ((rg_state == IDLE) || (rg_state == VALID_B16));
         w_addr <= addr;
      endmethod

      // CPU side: IMem response
      method ActionValue #(Tuple2 #(Instr, Maybe #(Exc_Code))) instr if (isValid (rg_instr));
         rg_instr <= tagged Invalid;
         return (tuple2 (rg_instr.Valid, rg_exc));
      endmethod
   endinterface
endmodule

// ================================================================

endpackage
