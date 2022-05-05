// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package EX_ALU_functions;

// ================================================================
// These are the "ALU" functions in the EX stage of the "Piccolo" CPU.
// EX stands for "Execution".

// ================================================================
// Exports

//export
//ALU_Inputs (..),
//ALU_Outputs (..),
//Completion_Info (..),
//fv_ALU;

// ================================================================
// BSV library imports

import Vector :: *;

// ----------------
// BSV additional libs

// None

// ================================================================
// Project imports

import ISA_Decls   :: *;
import CPU_Globals :: *;
`ifdef INCLUDE_TANDEM_VERIF
import TV_Info     :: *;
`endif

// ================================================================
// EXEC1 inputs
typedef struct {
   Instr          instr;
`ifdef ISA_C
   Bool           is_i32_not_i16;
   Instr_C        instr_C;
`endif
   Decoded_uControl ucontrol;
   WordXL         rs1_val;
   WordXL         rs2_val;
`ifdef ISA_F
   Bit #(3)       frm;
   WordFL         frs1_val;
   WordFL         frs2_val;
   WordFL         frs3_val;
`ifdef INCLUDE_TANDEM_VERIF
   Bit #(5)       fflags;
`endif
`endif
} EXEC1_Inputs deriving (Bits, FShow);

// ALU inputs

typedef struct {
`ifndef MIN_CSR
   Priv_Mode      cur_priv;         // XXX: consider removing
   MISA           misa;             // XXX: consider removing
   WordXL         mstatus;          // XXX: consider removing
`endif
   Addr           pc;
   Instr          instr;
`ifdef ISA_C
   Bool           is_i32_not_i16;
`endif
   Decoded_uControl ucontrol;
   WordXL         rs1_val;
   WordXL         rs2_val;
`ifdef ISA_F
   // Replace mstatus with mstatus.fs
   Bit #(3)       frm;
   WordFL         frs1_val;
   WordFL         frs2_val;
   WordFL         frs3_val;
`ifdef INCLUDE_TANDEM_VERIF
   Bit #(5)       fflags;
`endif
`endif
`ifdef ISA_PRIV_S
   // XXX Replace mstatus with mstatus.tvm and mstatus.tsr
`endif
   } ALU_Inputs
deriving (Bits, FShow);

// ----------------
// These functions pick the instruction size and instruction bits to
// be sent in the trace to a tandem verifier

function ISize  fv_trace_isize (ALU_Inputs  inputs);
`ifdef ISA_C
   return (inputs.is_i32_not_i16 ? ISIZE32BIT : ISIZE16BIT);
`else
   return (ISIZE32BIT);
`endif
endfunction

`ifdef INCLUDE_TANDEM_VERIF
function Bit #(32)  fv_trace_instr (ALU_Inputs  inputs);
   Bit #(32) result = inputs.instr;
`ifdef ISA_C
   if (! inputs.is_i32_not_i16)
      result = zeroExtend (inputs.instr_C);
`endif
   return result;
endfunction
`endif

// ================================================================
// ALU outputs

typedef struct {
   Control    control;
   Exc_Code   exc_code;        // Relevant if control == CONTROL_TRAP

   Op_Stage2  op_stage2;
   RegName    rd;
   Addr       addr;           // Branch, jump: newPC
		              // Mem ops and AMOs: mem addr
   WordXL     val1;           // OP_Stage2_ALU: result for Rd (ALU ops: result, JAL/JALR: return PC)
                              // CSRRx: rs1_val
                              // OP_Stage2_M: arg1
                              // OP_Stage2_AMO: funct7

   WordXL     val2;           // Branch: branch target (for Tandem Verification)
		              // OP_Stage2_ST: store-val
                              // OP_Stage2_M: arg2
`ifdef ISA_F
   WordFL     fval1;          // OP_Stage2_FD: arg1
   WordFL     fval2;          // OP_Stage2_FD: arg2
   WordFL     fval3;          // OP_Stage2_FD: arg3
   Bool       rd_in_fpr;      // result to be written to fpr
   Bool       rs_frm_fpr;     // src register is in fpr (for stores)
   Bool       val1_frm_gpr;   // first operand is in gpr (for some FP instrns)
   Bit #(3)   rm;             // rounding mode
`endif

`ifdef INCLUDE_TANDEM_VERIF
   Trace_Data trace_data;
`endif
   } ALU_Outputs
deriving (Bits, FShow);

ALU_Outputs alu_outputs_base
= ALU_Outputs {
     control     : CONTROL_STRAIGHT
   , exc_code    : exc_code_ILLEGAL_INSTRUCTION
   , op_stage2   : OP_Stage2_ALU
   , rd          : ?
   , addr        : ?
   , val1        : ?
   , val2        : ?
`ifdef ISA_F    
   , fval1       : ?
   , fval2       : ?
   , fval3       : ?
   , rd_in_fpr   : False
   , rs_frm_fpr  : False
   , val1_frm_gpr: False
   , rm          : ?
`endif

`ifdef INCLUDE_TANDEM_VERIF
   , trace_data  : ?
`endif
};

// This structure is extracted from the elements of ALU_Outputs
// and is the information required by the COMPLETION states of the
// Magritte FSM.
typedef struct {
   Instr      instr;
   RegName    rd;
   Addr       addr;           // Branch, jump: newPC
		              // Mem ops and AMOs: mem addr
   WordXL     val1;           // OP_Stage2_ALU: result for Rd (ALU ops: result, JAL/JALR: return PC)
                              // CSRRx: rs1_val
                              // OP_Stage2_M: arg1
                              // OP_Stage2_AMO: funct7

   WordXL     val2;           // Branch: branch target (for Tandem Verification)
		              // OP_Stage2_ST: store-val
                              // OP_Stage2_M: arg2
`ifdef ISA_F
   Bool       rd_in_fpr;      // result to be written to fpr
`endif
} Completion_Info deriving (Bits, FShow);


// ================================================================
// The fall-through PC is PC+4 for normal 32b instructions,
// and PC+2 for 'C' (16b compressed) instructions.

function Addr fall_through_pc (ALU_Inputs  inputs);
   Addr next_pc = inputs.pc + 4;
`ifdef ISA_C
   if (! inputs.is_i32_not_i16)
      next_pc = inputs.pc + 2;
`endif
   return next_pc;
endfunction

// ================================================================
// Alternate implementation of shifts using multiplication in DSPs

// ----------------------------------------------------------------
/* TODO: DELETE? 'factor' RegFile for shift ops

// ----------------------------------------------------------------
// The following is a lookup table of multiplication factors used by the "shift" ops
RegFile #(Bit #(TLog #(XLEN)), Bit #(XLEN))  rf_sh_factors <- mkRegFileFull;
// The following is used during reset to initialize rf_sh_factors
Reg #(Bool)                                  rg_resetting  <- mkReg (False);
Reg #(Bit #(TAdd #(1, TLog #(XLEN))))        rg_j          <- mkRegU;
Reg #(WordXL)                                rg_factor     <- mkRegU;
*/

// ----------------------------------------------------------------
// The following functions implement the 'shift' operators SHL, SHRL and SHRA
// using multiplication instead of actual shifts,
// thus using DSPs (multiplication) and LUTRAMs (rf_sh_factors) instead of LUTs

// Shift-left
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs.
// To SHL(n), do a multiplication by 2^n.
// The 2^n factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shl (WordXL x, Bit #(TLog #(XLEN)) shamt);
   IntXL  x_signed = unpack (x);

   // IntXL y_signed = unpack (rf_sh_factors.sub (shamt));
   IntXL  y_signed = unpack ('b1 << shamt);

   IntXL  z_signed = x_signed * y_signed;
   WordXL z        = pack (z_signed);
   return z;
endfunction

// Shift-right-arithmetic
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs
// To SHR(n), do a 2*XLEN-wide multiplication by 2^(32-n), and take upper XLEN bits
// The 2^(32-n) factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shra (WordXL x, Bit #(TLog #(XLEN)) shamt);
   // Bit #(TAdd #(1, XLEN)) y = { reverseBits (rf_sh_factors.sub (shamt)), 1'b0 };
   Bit #(TAdd #(1, XLEN)) y = { reverseBits ('b1 << shamt), 1'b0 };

   Int #(XLEN_2) xx_signed = extend (unpack (x));
   Int #(XLEN_2) yy_signed = unpack (extend (y));
   Int #(XLEN_2) zz_signed = xx_signed * yy_signed;
   Bit #(XLEN_2) zz        = pack (zz_signed);
   WordXL        z         = truncateLSB (zz);
   return z;
endfunction

// Shift-right-logical
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs
// To SHR(n), do a 2*XLEN-wide multiplication by 2^(32-n), and take upper XLEN bits
// The 2^(32-n) factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shrl (WordXL x, Bit #(TLog #(XLEN)) shamt);
   // Bit #(TAdd #(1, XLEN)) y = { reverseBits (rf_sh_factors.sub (shamt)), 1'b0 };
   Bit #(TAdd #(1, XLEN)) y = { reverseBits ('b1 << shamt), 1'b0 };

   Bit #(XLEN_2) xx = extend (x);
   Bit #(XLEN_2) yy = extend (y);
   Bit #(XLEN_2) zz = xx * yy;
   WordXL        z  = truncateLSB (zz);
   return z;
endfunction

// ================================================================
// BRANCH

function ALU_Outputs fv_BRANCH (ALU_Inputs inputs);
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (inputs.rs1_val);
   IntXL s_rs2_val = unpack (inputs.rs2_val);

   let   imm13_SB      = instr_SB_imm13 (inputs.instr);
   IntXL offset        = extend (unpack (imm13_SB));
   Addr  branch_target = pack (unpack (inputs.pc) + offset);
   Bool  branch_taken  = False;
   Bool  trap          = False;

   if      (inputs.ucontrol.f3.is_f3_BEQ)  branch_taken = (rs1_val  == rs2_val);
   else if (inputs.ucontrol.f3.is_f3_BNE)  branch_taken = (rs1_val  != rs2_val);
   else if (inputs.ucontrol.f3.is_f3_BLT)  branch_taken = (s_rs1_val <  s_rs2_val);
   else if (inputs.ucontrol.f3.is_f3_BGE)  branch_taken = (s_rs1_val >= s_rs2_val);
   else if (inputs.ucontrol.f3.is_f3_BLTU) branch_taken = (rs1_val  <  rs2_val);
   else if (inputs.ucontrol.f3.is_f3_BGEU) branch_taken = (rs1_val  >= rs2_val);
   else                                    trap = True;

   Bool misaligned_target = (branch_target [1] == 1'b1);
`ifdef ISA_C
   misaligned_target = False;
`endif

   Exc_Code exc_code = exc_code_ILLEGAL_INSTRUCTION;
   if ((! trap) && branch_taken && misaligned_target) begin
      trap = True;
      exc_code = exc_code_INSTR_ADDR_MISALIGNED;
   end

   let alu_outputs = alu_outputs_base;
   let next_pc     = (branch_taken ? branch_target : fall_through_pc (inputs));
   alu_outputs.control   = (trap ? CONTROL_TRAP
                                 : (branch_taken ? CONTROL_BRANCH
                                                 : CONTROL_STRAIGHT));
   alu_outputs.exc_code  = exc_code;
   alu_outputs.rd        = 0;
   alu_outputs.addr      = next_pc;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   // XXX Revisit
   alu_outputs.val2      = extend (branch_target);    // For tandem verifier only
   alu_outputs.trace_data = mkTrace_OTHER (next_pc,
					   fv_trace_isize (inputs),
					   fv_trace_instr (inputs));
`endif
   return alu_outputs;
endfunction


// ----------------------------------------------------------------
// JAL

function ALU_Outputs fv_JAL (ALU_Inputs inputs);
   IntXL offset  = extend (unpack (instr_UJ_imm21(inputs.instr)));
   Addr  next_pc = pack (unpack (inputs.pc) + offset);
   Addr  ret_pc  = fall_through_pc (inputs);

   Bool misaligned_target = (next_pc [1] == 1'b1);
`ifdef ISA_C
   misaligned_target = False;
`endif

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = (misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH);
   alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
   alu_outputs.addr      = next_pc;
   alu_outputs.val1      = extend (ret_pc);

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   // XXX Revisit
   alu_outputs.trace_data = mkTrace_I_RD (next_pc,
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  instr_rd (inputs.instr),
					  ret_pc);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// JALR

function ALU_Outputs fv_JALR (ALU_Inputs inputs);
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (rs1_val);
   IntXL s_rs2_val = unpack (rs2_val);
   IntXL offset    = extend (unpack (instr_I_imm12 (inputs.instr)));
   Addr  next_pc   = pack (s_rs1_val + offset);
   Addr  ret_pc    = fall_through_pc (inputs);

   // next_pc [0] should be cleared
   next_pc [0] = 1'b0;

   Bool misaligned_target = (next_pc [1] == 1'b1);
`ifdef ISA_C
   misaligned_target = False;
`endif

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = (misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH);
   alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
   alu_outputs.addr      = next_pc;
   alu_outputs.val1      = extend (ret_pc);

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (next_pc,
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  instr_rd (inputs.instr),
					  ret_pc);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// Integer Register-Register and Register-Immediate Instructions

// ----------------
// Shifts (funct3 == f3_SLLI/ f3_SRLI/ f3_SRAI)

function ALU_Outputs fv_OP_and_OP_IMM_shifts (ALU_Inputs inputs);
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;
   let imm12   = instr_I_imm12 (inputs.instr);

   IntXL s_rs1_val = unpack (rs1_val);    // Signed version of rs1, for SRA

   Bit #(TLog #(XLEN)) shamt = (  (inputs.ucontrol.opcode.is_op_OP_IMM)
				? truncate (imm12)
				: truncate (rs2_val));

   WordXL   rd_val    = ?;
   Bit #(1) instr_b30 = inputs.instr [30];
   let alu_outputs    = alu_outputs_base;

`ifdef SHIFT_BARREL
   // Shifts implemented by Verilog synthesis,
   // mapping to barrel shifters
   if (inputs.ucontrol.f7.is_f7_ADD && inputs.ucontrol.f3.is_f3_SLL)
      rd_val = (rs1_val << shamt);
   else        // assert: (funct3 == f3_SRxI)
      rd_val = (inputs.ucontrol.f7.is_f7_ADD) ? (rs1_val >> shamt)
                                              : pack (s_rs1_val >> shamt);
   alu_outputs.val1      = rd_val;
`endif

`ifdef SHIFT_MULT
   // Shifts implemented using multiplication by 2^shamt,
   // mapping to DSPs in FPGA
   if (inputs.ucontrol.f7.is_f7_ADD && inputs.ucontrol.f3.is_f3_SLL)
      rd_val = fn_shl (rs1_val, shamt);  // in LUTRAMs/DSPs
   else // assert: (funct3 == f3_SRxI)
      rd_val = (inputs.ucontrol.f7.is_f7_ADD) ? fn_shrl (rs1_val, shamt)   // in LUTRAMs/DSPs
                                              : fn_shra (rs1_val, shamt);  // in LUTRAMs/DSPs
   alu_outputs.val1      = rd_val;
`endif

`ifdef SHIFT_SERIAL
   // Will be executed in serial Shifter_Box later
   alu_outputs.op_stage2 = OP_Stage2_SH;
   alu_outputs.val1      = rs1_val;
   // Encode 'arith-shift' in bit [7] of val2
   WordXL val2 = extend (shamt);
   val2 = (val2 | { 0, instr_b30, 7'b0});
   alu_outputs.val2 = val2;
`endif

   // Trap in RV32 if shamt > 31, i.e., if imm12 [5] is 1
   Bool trap = ((rv_version == RV32) && (imm12 [5] == 1));
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  instr_rd (inputs.instr),
					  rd_val);
`endif
   return alu_outputs;
endfunction: fv_OP_and_OP_IMM_shifts
  
// And-Or mux that works with one-hot encoded selects. 
// One select line must be enabled.
function Bit#(t) fv_and_or_mux (Vector #(n, Bool) v_selects, Vector #(n, Bit# (t)) v_values)
   provisos (Add#(1, b__, n));
   function Bit #(t) fv_and (Bit #(t) a, Bit #(t) b);
      return (a & b);
   endfunction 

   // replicates the boolean select signal into a Bit# (t) pattern
   function Bit #(t) fv_bool_to_bits (Bool sel);
      Vector #(t, Bit#(1)) v_sel = replicate (pack (sel));
      return (pack (v_sel));
   endfunction

   let v_ext_selects = map (fv_bool_to_bits, v_selects);

   // AND with selects
   let v_anded_values = zipWith (fv_and, v_values, v_ext_selects);

   // OR all the and-terms
   return (fold (\| , v_anded_values));
endfunction
  
// ----------------
// Remaining OP and OP_IMM (excluding shifts, M ops MUL/DIV/REM)

function ALU_Outputs fv_OP_and_OP_IMM (ALU_Inputs inputs);
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;
   let imm12   = instr_I_imm12 (inputs.instr);

   // Signed versions of rs1_val and rs2_val
   IntXL  s_rs1_val = unpack (rs1_val);
   IntXL  s_rs2_val = unpack (rs2_val);

   IntXL  s_rs2_val_local = s_rs2_val;
   WordXL rs2_val_local   = rs2_val;

   Bit #(1) instr_b30  = inputs.instr [30];
   Bool     subtract   = (inputs.ucontrol.opcode.is_op_OP) && (instr_b30 == 1'b1);

   if (inputs.ucontrol.opcode.is_op_OP_IMM) begin
      s_rs2_val_local = extend (unpack (imm12));
      rs2_val_local   = pack (s_rs2_val_local);
   end

   Vector #(7, Bool) sels = newVector;
   Vector #(7, WordXL) vals = newVector;
   let f3 = inputs.ucontrol.f3;

   sels[0] = (f3.is_f3_ADD && !subtract); vals[0] = pack (s_rs1_val + s_rs2_val_local);
   sels[1] = (f3.is_f3_ADD &&  subtract); vals[1] = pack (s_rs1_val - s_rs2_val_local);
   sels[2] = (f3.is_f3_SLT)             ; vals[2] = ((s_rs1_val < s_rs2_val_local) ? 1 : 0);
   sels[3] = (f3.is_f3_SLTU)            ; vals[3] = ((rs1_val  < rs2_val_local)  ? 1 : 0);
   sels[4] = (f3.is_f3_XOR)             ; vals[4] = pack (s_rs1_val ^ s_rs2_val_local);
   sels[5] = (f3.is_f3_OR)              ; vals[5] = pack (s_rs1_val | s_rs2_val_local);
   sels[6] = (f3.is_f3_AND)             ; vals[6] = pack (s_rs1_val & s_rs2_val_local);

   let trap = !fold (\|| , sels);
   let rd_val = fv_and_or_mux (sels, vals);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  instr_rd (inputs.instr),
					  rd_val);
`endif
   return alu_outputs;
endfunction: fv_OP_and_OP_IMM

`ifdef RV64
// ----------------
// OP_IMM_32 (ADDIW, SLLIW, SRxIW)

function ALU_Outputs fv_OP_IMM_32 (ALU_Inputs inputs);
   WordXL   rs1_val     = inputs.rs1_val;
   IntXL    s_rs1_val   = unpack (rs1_val);
   let      imm12       = instr_I_imm12 (inputs.instr);

   Bit #(5) shamt       = truncate (imm12);
   Bool     shamt5_is_0 = (inputs.instr [25] == 1'b0);

   let    funct3 = inputs.decoded_instr.funct3;
   Bool   trap   = False;
   WordXL rd_val = ?;

   if (inputs.ucontrol.f3.is_f3_ADD) begin
      IntXL  s_rs2_val = extend (unpack (imm12));
      IntXL  sum       = s_rs1_val + s_rs2_val;
      WordXL tmp       = pack (sum);
      rd_val           = signExtend (tmp [31:0]);
   end
   else if ((inputs.ucontrol.f3.is_f3_SLL) && shamt5_is_0) begin
      Bit #(32) tmp = truncate (rs1_val);
      rd_val = signExtend (tmp << shamt);
   end
   else if ((inputs.ucontrol.f3.is_f3_SRx) && shamt5_is_0) begin
      Bit #(1) instr_b30 = inputs.instr [30];
      if (instr_b30 == 1'b0) begin
	 // SRLIW
	 Bit #(32) tmp = truncate (rs1_val);
	 rd_val = signExtend (tmp >> shamt);
      end
      else begin
	 // SRAIW
	 Int #(32) s_tmp = unpack (rs1_val [31:0]);
	 Bit #(32) tmp   = pack (s_tmp >> shamt);
	 rd_val = signExtend (tmp);
      end
   end
   else
      trap = True;

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  instr_rd (inputs.instr),
					  rd_val);
`endif
   return alu_outputs;
endfunction: fv_OP_IMM_32

// ----------------
// OP_32 (excluding 'M' ops: MULW/ DIVW/ DIVUW/ REMW/ REMUW)

function ALU_Outputs fv_OP_32 (ALU_Inputs inputs);
   Bit #(32) rs1_val = inputs.rs1_val [31:0];
   Bit #(32) rs2_val = inputs.rs2_val [31:0];

   // Signed version of rs1_val and rs2_val
   Int #(32) s_rs1_val = unpack (rs1_val);
   Int #(32) s_rs2_val = unpack (rs2_val);

   Bit #(1) instr_b30  = inputs.instr [30];
   Bool     subtract   = (inputs.ucontrol.opcode.is_op_OP_32) && (instr_b30 == 1'b1);

   WordXL rd_val = ?;

   if (inputs.ucontrol.f3.is_f3_ADD) begin
      rd_val = subtract ? pack (signExtend (s_rs1_val - s_rs2_val))
                        : pack (signExtend (s_rs1_val + s_rs2_val));
   end

   if (inputs.ucontrol.f3.is_f3_SLL) rd_val = pack (signExtend (rs1_val << (rs2_val [4:0])));
   if (inputs.ucontrol.f3.is_f3_SRx) begin
      rd_val = subtract ? pack (signExtend (s_rs1_val >> (rs2_val [4:0])));
                        : pack (signExtend (rs1_val >> (rs2_val [4:0])));
   end

   Bool trap = !(   inputs.ucontrol.f3.is_f3_ADD
                 || inputs.ucontrol.f3.is_f3_SLL
                 || inputs.ucontrol.f3.is_f3_SRx);


   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  instr_rd (inputs.instr),
					  rd_val);
`endif
   return alu_outputs;
endfunction: fv_OP_32
`endif

// ----------------------------------------------------------------
// Upper Immediates

function ALU_Outputs fv_LUI (ALU_Inputs inputs);
   Bit #(32)  v32    = { instr_U_imm20 (inputs.instr), 12'h0 };
   IntXL      iv     = extend (unpack (v32));
   let        rd_val = pack (iv);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // XXX Revisit after PoC
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  instr_rd (inputs.instr),
					  rd_val);
`endif
   return alu_outputs;
endfunction

function ALU_Outputs fv_AUIPC (ALU_Inputs inputs);
   IntXL  iv     = extend (unpack ({ instr_U_imm20 (inputs.instr), 12'b0}));
   IntXL  pc_s   = unpack (inputs.pc);
   WordXL rd_val = pack (pc_s + iv);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // XXX Revisit after PoC
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  instr_rd (inputs.instr),
					  rd_val);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// LOAD

function ALU_Outputs fv_LD (ALU_Inputs inputs);
   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (inputs.rs1_val);
   IntXL s_rs2_val = unpack (inputs.rs2_val);
   let imm12   = instr_I_imm12 (inputs.instr);

   IntXL  imm_s = extend (unpack (imm12));
   WordXL eaddr = pack (s_rs1_val + imm_s);

   Bool legal_LD = inputs.ucontrol.f3.is_LDST_legal;

   // FP loads are not legal unless the MSTATUS.FS bit is set
   Bool legal_FP_LD = True;
`ifdef ISA_F
   if (inputs.ucontrol.opcode.is_op_LOAD_FP)
      legal_FP_LD = (fv_mstatus_fs (inputs.mstatus) != fs_xs_off);
`endif

   let alu_outputs = alu_outputs_base;

   alu_outputs.control   = ((legal_LD && legal_FP_LD) ? CONTROL_STRAIGHT
                                                      : CONTROL_TRAP);
   alu_outputs.op_stage2 = OP_Stage2_LD;
   alu_outputs.addr      = eaddr;
`ifdef ISA_F
   // note that the destination register for this load is in the FPR
   alu_outputs.rd_in_fpr = inputs.ucontrol.opcode.is_op_LOAD_FP;
`endif

`ifdef INCLUDE_TANDEM_VERIF
   // XXX Revisit after PoC
   // Normal trace output (if no trap)
`ifdef ISA_F
   if (alu_outputs.rd_in_fpr)
      alu_outputs.trace_data = mkTrace_F_LOAD (fall_through_pc (inputs),
					       fv_trace_isize (inputs),
					       fv_trace_instr (inputs),
					       inputs.decoded_instr.rd,
					       ?,
					       eaddr,
                                               inputs.mstatus);
   else
`endif
      alu_outputs.trace_data = mkTrace_I_LOAD (fall_through_pc (inputs),
					       fv_trace_isize (inputs),
					       fv_trace_instr (inputs),
					       inputs.decoded_instr.rd,
					       ?,
					       eaddr);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// STORE

function ALU_Outputs fv_ST (ALU_Inputs inputs);
   // Signed version of rs1_val
   IntXL  s_rs1_val = unpack (inputs.rs1_val);
   let    imm12     = instr_S_imm12 (inputs.instr);
   IntXL  imm_s     = extend (unpack (imm12));
   WordXL eaddr     = pack (s_rs1_val + imm_s);

   Bool legal_ST = inputs.ucontrol.f3.is_LDST_legal;

   let alu_outputs = alu_outputs_base;

   // FP stores are not legal unless the MSTATUS.FS bit is set
   Bool legal_FP_ST = True;
`ifdef ISA_F
   if (inputs.ucontrol.opcode.is_op_STORE_FP) begin
      legal_FP_ST = (fv_mstatus_fs (inputs.mstatus) != fs_xs_off);

      // note that the source data register for this store is in the FPR
      alu_outputs.rs_frm_fpr = True;
   end
`endif

   alu_outputs.control   = ((legal_ST && legal_FP_ST) ? CONTROL_STRAIGHT
                                                      : CONTROL_TRAP);
   alu_outputs.op_stage2 = OP_Stage2_ST;
   alu_outputs.addr      = eaddr;

   alu_outputs.val2      = inputs.rs2_val;

`ifdef ISA_F
   alu_outputs.fval2     = inputs.frs2_val;
`endif

`ifdef INCLUDE_TANDEM_VERIF
   // XXX Revisit after PoC
   // Normal trace output (if no trap)
`ifdef ISA_F
   if (inputs.ucontrol.opcode.is_op_STORE_FP)
      alu_outputs.trace_data = mkTrace_F_STORE (fall_through_pc (inputs),
						funct3,
						fv_trace_isize (inputs),
						fv_trace_instr (inputs),
						alu_outputs.fval2,
						eaddr);
   else
`endif
      alu_outputs.trace_data = mkTrace_I_STORE (fall_through_pc (inputs),
						funct3,
						fv_trace_isize (inputs),
						fv_trace_instr (inputs),
						(alu_outputs.val2),
						eaddr);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// MISC_MEM (FENCE and FENCE.I)
// nops, on Magritte-TCM

function ALU_Outputs fv_MISC_MEM (ALU_Inputs inputs);
   let alu_outputs = alu_outputs_base;
   alu_outputs.control  = (  (inputs.ucontrol.f3.is_f3_FENCE_I)
			   ? CONTROL_FENCE_I
			   : (  (inputs.ucontrol.f3.is_f3_FENCE)
			      ? CONTROL_FENCE
			      : CONTROL_TRAP));

`ifdef INCLUDE_TANDEM_VERIF
   // XXX Revisit after PoC
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_OTHER (fall_through_pc (inputs),
					   fv_trace_isize (inputs),
					   fv_trace_instr (inputs));
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// System instructions

function ALU_Outputs fv_SYSTEM (ALU_Inputs inputs);
   let alu_outputs = alu_outputs_base;
   let funct3  = instr_funct3 (inputs.instr);
   let imm12   = instr_I_imm12 (inputs.instr);
   let rd      = instr_rd (inputs.instr);
   let rs1     = instr_rs1 (inputs.instr);

`ifdef INCLUDE_TANDEM_VERIF
   // XXX Revisit after PoC
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_OTHER (fall_through_pc (inputs),
					   fv_trace_isize (inputs),
					   fv_trace_instr (inputs));
`endif

   if (inputs.ucontrol.f3.is_f3_PRIV) begin
`ifdef ISA_PRIV_S
      // SFENCE.VMA instruction
      if (   (rd == 0)
	  && (   (inputs.cur_priv == m_Priv_Mode)
	      || (   (inputs.cur_priv == s_Priv_Mode)
		  && (inputs.mstatus [mstatus_tvm_bitpos] == 0)))
	  && (inputs.ucontrol.f7.is_f7_SFENCE_VMA))
	 begin
	    alu_outputs.control = CONTROL_SFENCE_VMA;
	 end
      else
`endif
      if ((rd  == 0) && (rs1 == 0))
	 begin
	    // ECALL instructions
	    if (inputs.ucontrol.f12.is_f12_ECALL) begin
	       alu_outputs.control  = CONTROL_TRAP;
`ifdef MIN_CSR
	       alu_outputs.exc_code = exc_code_ECALL_FROM_M;
`else
	       alu_outputs.exc_code = ((inputs.cur_priv == u_Priv_Mode)
				       ? exc_code_ECALL_FROM_U
				       : ((inputs.cur_priv == s_Priv_Mode)
					  ? exc_code_ECALL_FROM_S
					  : exc_code_ECALL_FROM_M));
`endif
	    end

	    // EBREAK instruction
	    else if (inputs.ucontrol.f12.is_f12_EBREAK) begin
	       alu_outputs.control  = CONTROL_TRAP;
	       alu_outputs.exc_code = exc_code_BREAKPOINT;
	    end

	    // MRET instruction
`ifdef MIN_CSR
	    else if ((inputs.ucontrol.f12.is_f12_MRET))
`else
	    else if (   (inputs.cur_priv >= m_Priv_Mode)
		     && (inputs.ucontrol.f12.is_f12_MRET))
`endif
	       begin
		  alu_outputs.control = CONTROL_MRET;
	       end

`ifdef ISA_PRIV_S
	    // SRET instruction
	    else if (   (   (inputs.cur_priv == m_Priv_Mode)
			 || (   (inputs.cur_priv == s_Priv_Mode)
			     && (inputs.mstatus [mstatus_tsr_bitpos] == 0)))
		     && (inputs.ucontrol.f12.is_f12_SRET))
	       begin
		  alu_outputs.control = CONTROL_SRET;
	       end
`endif

	    /*
	    // URET instruction (future: Piccolo does not support 'N' extension)
	    else if (   (inputs.cur_priv >= u_Priv_Mode)
		     && (inputs.decoded_instr.imm12_I == f12_URET))
	       begin
		  alu_outputs.control = CONTROL_URET;
	       end
	    */

	    // WFI instruction
`ifdef MIN_CSR
            // With CSR_Regfile_Min there is a single privilege level (M)
            // MSTATUS.TW bit is always 0. MISA.N = 0.
	    else if (inputs.ucontrol.f12.is_f12_WFI) begin
`else
	    else if (   (   (inputs.cur_priv == m_Priv_Mode)
			 || (   (inputs.cur_priv == s_Priv_Mode)
			     && (inputs.mstatus [mstatus_tw_bitpos] == 0))
			 || (   (inputs.cur_priv == u_Priv_Mode)
			     && (inputs.misa.n == 1)))
		     && (inputs.ucontrol.f12.is_f12_WFI))
	       begin
`endif
               alu_outputs.control = CONTROL_WFI;
	    end

	    else begin
	       alu_outputs.control = CONTROL_TRAP;
	    end
	 end

      else begin
	 alu_outputs.control = CONTROL_TRAP;
      end
   end    // inputs.ucontrol.f3.is_f3_PRIV

   // CSRRW, CSRRWI
   else if (f3_is_CSRR_W (inputs.ucontrol.f3)) begin
      WordXL rs1_val = (  (funct3[2] == 1)
			? extend (rs1)       // Immediate zimm
			: inputs.rs1_val);   // From rs1 reg

      alu_outputs.control   = CONTROL_CSRR_W;
      alu_outputs.val1      = rs1_val;
   end

   // CSRRS, CSRRSI, CSRRC, CSRRCI
   else if (f3_is_CSRR_S_or_C (inputs.ucontrol.f3)) begin
      WordXL rs1_val = (  (funct3 [2] == 1)
			? extend (rs1)       // Immediate zimm
			: inputs.rs1_val);   // From rs1 reg

      alu_outputs.control   = CONTROL_CSRR_S_or_C;
      alu_outputs.val1      = rs1_val;
   end

   // funct3 is not f3_PRIV
   else begin // (funct3 == f3_SYSTEM_ILLEGAL)
      alu_outputs.control = CONTROL_TRAP;
   end

   return alu_outputs;
endfunction: fv_SYSTEM

// ----------------------------------------------------------------
// FP Ops
// Just pass through to the FP stage

`ifdef ISA_F
function ALU_Outputs fv_FP (ALU_Inputs inputs);
   let opcode = inputs.decoded_instr.opcode;
   let funct3 = inputs.decoded_instr.funct3;
   let funct7 = inputs.decoded_instr.funct7;
   let rs2    = inputs.decoded_instr.rs2;

   // Check instruction legality
   // Is the rounding mode legal
   match {.rm, .rm_is_legal} = fv_rmode_check  (funct3, inputs.frm);

   // Is the instruction legal -- if MSTATUS.FS = fs_xs_off, FP instructions
   // are always illegal
   let inst_is_legal = (  (fv_mstatus_fs (inputs.mstatus) == fs_xs_off)
			? False
			: fv_is_fp_instr_legal (funct7,
						rm,
						rs2,
						opcode));

   let alu_outputs         = alu_outputs_base;
   alu_outputs.control     = ((inst_is_legal && rm_is_legal) ? CONTROL_STRAIGHT
			                                     : CONTROL_TRAP);
   alu_outputs.op_stage2   = OP_Stage2_FD;
   alu_outputs.rd          = inputs.decoded_instr.rd;
   alu_outputs.rm          = rm;

   // Operand values
   // The first operand may be from the FPR or GPR
   alu_outputs.val1_frm_gpr= fv_fp_val1_from_gpr (opcode, funct7, rs2);


   // Just copy the rs1_val values from inputs to outputs this covers cases
   // whenever val1 is from GPR
   alu_outputs.val1     = inputs.rs1_val;

   // Just copy the frs*_val values from inputs to outputs
   alu_outputs.fval1     = inputs.frs1_val;
   alu_outputs.fval2     = inputs.frs2_val;
   alu_outputs.fval3     = inputs.frs3_val;

   alu_outputs.rd_in_fpr = !fv_is_rd_in_GPR (funct7, rs2);

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   if (alu_outputs.rd_in_fpr)
      alu_outputs.trace_data = mkTrace_F_FRD (fall_through_pc (inputs),
					      fv_trace_isize (inputs),
					      fv_trace_instr (inputs),
					      inputs.decoded_instr.rd,
					      ?,
					      inputs.fflags,
					      inputs.mstatus);
   else
      alu_outputs.trace_data = mkTrace_F_GRD (fall_through_pc (inputs),
					      fv_trace_isize (inputs),
					      fv_trace_instr (inputs),
					      inputs.decoded_instr.rd,
					      ?,
					      inputs.fflags,
					      inputs.mstatus);
`endif
   return alu_outputs;
endfunction
`endif


// ----------------------------------------------------------------
// AMO
// Just pass through to the memory stage

`ifdef ISA_A
function ALU_Outputs fv_AMO (ALU_Inputs inputs);
   Bool legal_f5 = (   (inputs.ucontrol.f5.is_f5_AMO_LR)
                    || (inputs.ucontrol.f5.is_f5_AMO_SC)
		    || (inputs.ucontrol.f5.is_f5_AMO_ADD)
		    || (inputs.ucontrol.f5.is_f5_AMO_SWAP)
		    || (inputs.ucontrol.f5.is_f5_AMO_AND)
                    || (inputs.ucontrol.f5.is_f5_AMO_OR)
                    || (inputs.ucontrol.f5.is_f5_AMO_XOR)
		    || (inputs.ucontrol.f5.is_f5_AMO_MIN)
                    || (inputs.ucontrol.f5.is_f5_AMO_MINU)
		    || (inputs.ucontrol.f5.is_f5_AMO_MAX)
                    || (inputs.ucontrol.f5.is_f5_AMO_MAXU));

   Bool legal_width = (   (inputs.ucontrol.f3.is_f3_AMO_W)
`ifdef RV64
		       || (inputs.ucontrol.f3.is_f3_AMO_D)
`endif
                      );

   let eaddr = inputs.rs1_val;

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = ((legal_f5 && legal_width) ? CONTROL_STRAIGHT : CONTROL_TRAP);
   alu_outputs.op_stage2 = OP_Stage2_AMO;
   alu_outputs.addr      = eaddr;
   alu_outputs.val1      = zeroExtend (instr_funct7 (inputs.instr));
   alu_outputs.val2      = inputs.rs2_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_AMO (fall_through_pc (inputs),
					 funct3,
					 fv_trace_isize (inputs),
					 fv_trace_instr (inputs),
					 inputs.decoded_instr.rd, ?,
					 inputs.rs2_val,
					 eaddr);
`endif
   return alu_outputs;
endfunction
`endif

// ================================================================

endpackage
