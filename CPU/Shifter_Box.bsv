// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package Shifter_Box;

// ================================================================
// This contains a module that executes the RISC-V instructions:
//  SLL/SLLI    shift left  logical
//  SRL/SRLI    shift right logical
//  SRA/SRAI    shift right arithmetic
// using a serial shifter.  For shift amounts of 31 (63) bits, it can
// take up to 31 (63) ticks to compute the result, which is slow, but
// it's much cheaper in hardware resources than a 1-tick barrel
// shifter.

// ================================================================
// Exports

// ================================================================
// BSV Library imports

import Vector :: *;
import ClientServer :: *;
import GetPut :: *;
import FIFOF :: *;

// ----------------
// BSV additional libs

// None

// ================================================================
// Project imports

import ISA_Decls  :: *;
import EX_ALU_functions :: *;
import Shifter_IFC :: *;
import Cur_Cycle :: *;

`ifdef SHIFT_2
Integer shift_amt = 2;
`elsif SHIFT_4
Integer shift_amt = 4;
`elsif SHIFT_8
Integer shift_amt = 8;
`else
Integer shift_amt = 1;  // default (single iterative shifter)
`endif

// ================================================================

(* synthesize *)
module mkShifter_Box (Shifter_Box_IFC);
   Reg #(Bool)                rg_right       <- mkRegU;
   Reg #(Word)                rg_v1          <- mkRegU;
   Reg #(Bit #(TLog #(XLEN))) rg_shamt       <- mkReg(0);
   Reg #(Bool)                rg_arith_shift <- mkRegU;

   // Reset
   FIFOF #(Token) f_reset_rsps <- mkFIFOF1;

   // The 'execution_order' attibs below are to override the compiler
   // default which schedules 'req' before rl_sll/sra/srl.  But 'req',
   // 'valid' and 'word' are called in the same rule in the main
   // pipeline, and so should not have 'sll/sra/srl' in between them.

   // A hybrid shifter consisting of a wide shifter (configured with the
   // appropriate ifdef) and a serial shifter. When the remaining shift amount is
   // less than the width supported by the wide shifter, revert to serial shifting
   // Tradeoff: narrow shifter means fewer resources, more cycles.

   // Left shifts
   (* execution_order = "req, rl_sll" *)
   rule rl_sll ((! rg_right) && (rg_shamt != 0));
      let n_shamt = rg_shamt;
      if (rg_shamt < fromInteger (shift_amt)) begin
         // Serial shift
         rg_v1   <= (rg_v1 << 1);
         n_shamt = n_shamt - 1;
      end

      else begin
         rg_v1   <= (rg_v1 << fromInteger (shift_amt));
         n_shamt = n_shamt - fromInteger (shift_amt);
      end
      rg_shamt <= n_shamt;
   endrule

   // Arithmetic right-shifts
   (* execution_order = "req, rl_sra" *)
   rule rl_sra (rg_right && rg_arith_shift && (rg_shamt != 0));
      let n_shamt = rg_shamt;
      Word_S s_val = unpack (rg_v1);    // Signed value
      if (rg_shamt < fromInteger (shift_amt)) begin
         // Serial shift
         rg_v1 <= pack (s_val >> 1);
         n_shamt = n_shamt - 1;
      end

      else begin
         rg_v1 <= pack (s_val >> fromInteger (shift_amt));
         n_shamt = n_shamt - fromInteger (shift_amt);
      end
      rg_shamt <= n_shamt;
   endrule

   // Logical right shifts
   (* execution_order = "req, rl_srl" *)
   rule rl_srl (rg_right && (! rg_arith_shift) && (rg_shamt != 0));
      let n_shamt = rg_shamt;
      if (rg_shamt < fromInteger (shift_amt)) begin
         rg_v1 <= (rg_v1 >> 1);
         n_shamt = n_shamt - 1;
      end

      else begin
         rg_v1 <= (rg_v1 >> fromInteger (shift_amt));
         n_shamt = n_shamt - fromInteger (shift_amt);
      end
      rg_shamt <= n_shamt;
   endrule

   // ================================================================
   // INTERFACE

   // Reset
   interface Server server_reset;
      interface Put request;
         method Action put (Token t);
            rg_right       <= False;
            rg_v1          <= 0;
            rg_shamt       <= 0;
            rg_arith_shift <= False;

            f_reset_rsps.enq (?);
         endmethod
      endinterface

      interface Get response = toGet (f_reset_rsps);
   endinterface


   // MBox interface: request
   method Action  req (Bool right, Word v1, Word v2);
      rg_right       <= right;
      rg_v1          <= v1;
      rg_shamt       <= truncate (v2);
      rg_arith_shift <= unpack (v2 [7]);
   endmethod

   // SBox interface: response
   method Bool  valid;
      return (rg_shamt == 0);
   endmethod

   method Word  word;
      return rg_v1;
   endmethod
endmodule

// ================================================================

(* synthesize *)
module mkLog_Shifter_Box (Shifter_Box_IFC);
   // Debug verbosity: 0: no messages, 1: rule firings, 2: details
   Integer verbosity = 0;
   Reg #(Bool)                rg_right       <- mkRegU;
   Reg #(Word)                rg_v1          <- mkRegU;
   Reg #(Bit #(TLog #(XLEN))) rg_shamt       <- mkRegU;
   Reg #(Bool)                rg_arith_shift <- mkRegU;
   Reg #(Bit #(6))            rg_iteration   <- mkReg(0);

   // Reset
   FIFOF #(Token) f_reset_rsps <- mkFIFOF1;

   // The 'execution_order' attibs below are to override the compiler
   // default which schedules 'req' before rl_sll/sra/srl.  But 'req',
   // 'valid' and 'word' are called in the same rule in the main
   // pipeline, and so should not have 'sll/sra/srl' in between them.

   Vector #(5, Bool) stage_sel = newVector;
   stage_sel [0] = ((rg_iteration [0] == 1'b1) && (rg_shamt[0] == 1'b1));
   stage_sel [1] = ((rg_iteration [1] == 1'b1) && (rg_shamt[1] == 1'b1));
   stage_sel [2] = ((rg_iteration [2] == 1'b1) && (rg_shamt[2] == 1'b1));
   stage_sel [3] = ((rg_iteration [3] == 1'b1) && (rg_shamt[3] == 1'b1));
   stage_sel [4] = ((rg_iteration [4] == 1'b1) && (rg_shamt[4] == 1'b1));

   // Any of the selects are active
   Bool any_sel_active = fold (\|| , stage_sel);

   // Left shifts
   (* execution_order = "req, rl_sll" *)
   rule rl_sll ((! rg_right) && (rg_iteration[5] == 1'b0));
      rg_iteration <= rg_iteration << 1;

      Vector #(5, Word) n_v1 = newVector;
      n_v1[0] = rg_v1 << 1;
      n_v1[1] = rg_v1 << 2;
      n_v1[2] = rg_v1 << 4;
      n_v1[3] = rg_v1 << 8;
      n_v1[4] = rg_v1 << 16;

      // The and_or_mux expects one and only one select line to be set
      if (any_sel_active) rg_v1 <= fv_and_or_mux (stage_sel, n_v1);

      if (verbosity >= 1) begin
         $display ("%0d: %m.rl_sll: (rg_iteration %05b) (rg_shamt %d %05b)"
            , cur_cycle, rg_iteration, rg_shamt, rg_shamt);
         if (verbosity == 2)
            $display ("      (rg_v1 %08h)", rg_v1);
            $display ("      n_v1: ", fshow (n_v1));
            $display ("      sel: ",  fshow (stage_sel));
            $display ("      nxt_v1: ", fv_and_or_mux (stage_sel, n_v1));
      end
   endrule

   // Arithmetic right-shifts
   (* execution_order = "req, rl_sra" *)
   rule rl_sra (rg_right && rg_arith_shift && (rg_iteration[5] == 1'b0));
      Word_S s_val = unpack (rg_v1);    // Signed value
      rg_iteration <= rg_iteration << 1;

      Vector #(5, Word) n_v1 = newVector;
      n_v1[0] = pack (s_val >> 1);
      n_v1[1] = pack (s_val >> 2);
      n_v1[2] = pack (s_val >> 4);
      n_v1[3] = pack (s_val >> 8);
      n_v1[4] = pack (s_val >> 16);

      if (any_sel_active) rg_v1 <= fv_and_or_mux (stage_sel, n_v1);

      if (verbosity >= 1) begin
         $display ("%0d: %m.rl_sra: %d", cur_cycle, rg_iteration);
         if (verbosity == 2)
            $display ("      (s_val %08h)", s_val);
      end
   endrule

   // Logical right shifts
   (* execution_order = "req, rl_srl" *)
   rule rl_srl (rg_right && (! rg_arith_shift) && (rg_iteration[5] == 1'b0));
      rg_iteration <= rg_iteration << 1;
      Vector #(5, Word) n_v1 = newVector;
      n_v1[0] = rg_v1 >> 1;
      n_v1[1] = rg_v1 >> 2;
      n_v1[2] = rg_v1 >> 4;
      n_v1[3] = rg_v1 >> 8;
      n_v1[4] = rg_v1 >> 16;

      if (any_sel_active) rg_v1 <= fv_and_or_mux (stage_sel, n_v1);

      if (verbosity >= 1) begin
         $display ("%0d: %m.rl_srl: %d", cur_cycle, rg_iteration);
         if (verbosity == 2)
            $display ("      (rg_v1 %08h)", rg_v1);
      end
   endrule

   // ================================================================
   // INTERFACE
   // Reset
   interface Server server_reset;
      interface Put request;
         method Action put (Token t);
            rg_right       <= False;
            rg_v1          <= 0;
            rg_shamt       <= 0;
            rg_arith_shift <= False;
            rg_iteration   <= 0;

            f_reset_rsps.enq (?);
         endmethod
      endinterface

      interface Get response = toGet (f_reset_rsps);
   endinterface

   // SBox interface: request
   method Action  req (Bool right, Word v1, Word v2);
      rg_right       <= right;
      rg_v1          <= v1;
      rg_shamt       <= truncate (v2);
      rg_iteration   <= 6'b1;
      rg_arith_shift <= unpack (v2 [7]);
   endmethod

   // MBox interface: response
   method Bool  valid;
      return (rg_iteration[5] == 1'b1);
   endmethod

   method Word  word;
      return rg_v1;
   endmethod
endmodule
endpackage
