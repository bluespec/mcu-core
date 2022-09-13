// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

package CPU_Globals;

// ================================================================
// Types common to multiple CPU stages,
// including types communicated from stage to stage.

// ================================================================
// BSV library imports

// None

// ----------------
// BSV additional libs

// None

// ================================================================
// Project imports

import ISA_Decls :: *;

`ifdef INCLUDE_TANDEM_VERIF
import TV_Info   :: *;
`endif

// ================================================================
// Major States of CPU

// CPU_RUNNING    : Ifetch, decode, RF read
// CPU_EXEC1      : Stage1 of execution: Addr calc (LD, ST, Branches)
//                : ALU compute for OP and OP-IMM. Calc fall-through PC.
// CPU_EXEC2      : Retirement for OP, OP-IMM, Branches (fetch next instr)
//                : Dispatch for all multi-cycle ops. 
// CPU*COMPLETION : Retirement for all multi-cycle ops (fetch next instr)

// We are in RL_RUNNING state, rule 'rl_run', for all 1-cycle
// instructions (ALU, BRANCH, ...).
// Memory access, floating point, mult/div, fences, WFI are all
// multi-cycle rules, involving 'completion' states and rules to
// handle completion.

typedef enum {
     CPU_RESET1
   , CPU_RESET2
`ifdef INCLUDE_GDB_CONTROL
   , CPU_GDB_PAUSING      // On GDB breakpoint, while waiting for fence completion
`endif
   , CPU_DEBUG_MODE       // Stopped (normally for debugger) but also for TCM Loader
   , CPU_RUNNING          // Normal operation: Instruction fetch, decode, RF read
   , CPU_EXEC1            // Normal operation: Exec stage1
   , CPU_EXEC2            // Normal operation: Exec stage2 (retirement for RV32I)
   , CPU_LD_COMPLETION    // Normal operation: Exec stage3: LD retire
   , CPU_ST_COMPLETION    // Normal operation: Exec stage3: ST retire
`ifdef ISA_X
   , CPU_X_COMPLETION     // Normal operation: Exec stage3: X instr retire
`endif
   , CPU_CSRR_W_COMPLETION// Normal operation: Exec stage3: CSRR_W retire
   , CPU_CSRR_S_C_COMPLETION// Normal operation: Exec stage3: CSRR_S_C retire
`ifdef ISA_A
   , CPU_AMO_COMPLETION   // Normal operation: Exec stage3: AMO completion in NM
   , CPU_AMO_COMPLETION2  // Normal operation: Exec stage4: AMO retire?
`endif
`ifdef ISA_M
   , CPU_M_COMPLETION     // Normal operation: Exec stage3: M retire
`endif
`ifdef ISA_F
   , CPU_FD_COMPLETION    // Normal operation: Exec stage3: FD retire
`endif
`ifdef SHIFT_SERIAL
   , CPU_SH_COMPLETION    // Normal operation: Exec stage3: Shift retire
`endif
`ifdef MCU_LITE
   , CPU_ERROR
`else
   , CPU_TRAP
   , CPU_RESTART_TRAP     // Restart (fetch) after a trap (breaks timing path)
   , CPU_BREAK            // Prepare to BREAK
`endif
   , CPU_INTERRUPT_PENDING// Take interrupt
   , CPU_RESTART_EXT_INT  // Restart (fetch) after an ext interrupt
`ifdef ISA_PRIV_S
   , CPU_SFENCE_VMA_COMPLETION// Normal operation: Execution stage2: SFENCE.VM
`endif
   , CPU_WFI_PAUSED        // On WFI pause
} CPU_State deriving (Eq, Bits, FShow);


// ================================================================
// Trap information that flows along pipe stages.

typedef struct {
   Addr      epc;
   Exc_Code  exc_code;
   Addr      tval;
   } Pipe_Trap_Info
deriving (Bits, FShow);


// ================================================================
// Output from Stage 1

// Outputs from Stage1 to pipeline control
typedef enum {  CONTROL_DISCARD
              , CONTROL_STRAIGHT
              , CONTROL_BRANCH
              , CONTROL_CSRR_W
              , CONTROL_CSRR_S_or_C
`ifndef MCU_LITE
              , CONTROL_FENCE
              , CONTROL_FENCE_I
              , CONTROL_SFENCE_VMA
`endif
              , CONTROL_MRET
`ifdef ISA_PRIV_S
              , CONTROL_SRET
`endif
`ifdef ISA_PRIV_U
              , CONTROL_URET
`endif
              , CONTROL_WFI
              , CONTROL_TRAP
   } Control
deriving (Eq, Bits, FShow);

// ================================================================
// Data_Stage1_to_Stage2: Data output from Stage1 stage, input to DM stage

// Stage1 stage forwards, to DM, one of these 'opcodes'
// - ALU result (all non-mem, M and FD insructions)
// - DM request (Data Memory LD/ST/...)
// - Shifter Box request (SLL/SLLI, SRL/SRLI, SRA/SRAI)
// - MBox request (integer multiply/divide)
// - FDBox request (floating point ops)

typedef enum {  OP_Stage2_ALU         // Pass-through (non mem, M, FD, AMO)
              , OP_Stage2_LD
              , OP_Stage2_ST

`ifdef SHIFT_SERIAL
              , OP_Stage2_SH
`endif

`ifdef ISA_M
              , OP_Stage2_M
`endif

`ifdef ISA_A
              , OP_Stage2_AMO
`endif

`ifdef ISA_F
              , OP_Stage2_FD
`endif
   } Op_Stage2
deriving (Eq, Bits, FShow);

typedef struct {
   Priv_Mode  priv;
   Addr       pc;
   Instr      instr;             // For debugging. Just funct3, funct7 are
                                 // enough for functionality.
   Op_Stage2  op_stage2;
   RegName    rd;
   Addr       addr;              // Branch, jump: newPC
                                 // Mem ops and AMOs: mem addr
   WordXL     val1;              // OP_Stage2_ALU: rd_val
                                 // OP_Stage2_M

   WordXL     val2;              // OP_Stage2_ST: store-val;
                                 // OP_Stage2_M and OP_Stage2_FD: arg2

`ifdef ISA_F
   // Floating point fields
   WordFL     fval1;             // OP_Stage2_FD: arg1
   WordFL     fval2;             // OP_Stage2_FD: arg2
   WordFL     fval3;             // OP_Stage2_FD: arg3
   Bool       rd_in_fpr;         // The rd should update into FPR
   Bool       rs_frm_fpr;        // The rs is from FPR (FP stores)
   Bool       val1_frm_gpr;      // The val1 is from GPR for a FP instruction
   Bit #(3)   rounding_mode;     // rounding mode from fcsr_frm or instr.rm
`endif

`ifdef INCLUDE_TANDEM_VERIF
   Trace_Data  trace_data;
`endif
   } Data_Stage1_to_Stage2
deriving (Bits);

instance FShow #(Data_Stage1_to_Stage2);
   function Fmt fshow (Data_Stage1_to_Stage2 x);
      Fmt fmt =   $format ("data_to_Stage 2 {pc:%h  instr:%h  priv:%0d\n", x.pc, x.instr, x.priv);
      fmt = fmt + $format ("            op_stage2:", fshow (x.op_stage2), "  rd:%0d\n", x.rd);
      fmt = fmt + $format ("            addr:%h  val1:%h  val2:%h}",
                           x.addr, x.val1, x.val2);
`ifdef ISA_F
      fmt = fmt + $format ("\n");
      fmt = fmt + $format ("            fval1:%h  fval2:%h  fval3:%h}",
                           x.fval1, x.fval2, x.fval3);
`endif
      return fmt;
   endfunction
endinstance

// ================================================================
endpackage
