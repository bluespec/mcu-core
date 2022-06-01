// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

package CPU;

// ================================================================
// This is Bluespec's "Magritte" CPU, implementing the RISC-V ISA.
// - RV32/64, IMAFDC (GC), Privilege levels M,S,U
// - Optional Debug Module connection
// - Optional Tandem Verification connection.

// This implementation is built for simplicity and small size, not
// for architectural performance, hence implemented as an FSM,
// without any pipelining.  cf. "Ceci n'est pas une pipe" -- René
// Magritte ("This is not a pipe")

// ================================================================
// Exports

export mkCPU;

// ================================================================
// BSV library imports

import FIFOF         :: *;
import SpecialFIFOs  :: *;
import GetPut        :: *;
import ClientServer  :: *;
import Connectable   :: *;
import ConfigReg     :: *;

// ----------------
// BSV additional libs

import Cur_Cycle     :: *;
import GetPut_Aux    :: *;
import Semi_FIFOF    :: *;

// ================================================================
// Project imports

import AXI4_Types    :: *;
import Fabric_Defs   :: *;

`ifdef FABRIC_APB
import APB_Types     :: *;
import APB_Defs      :: *;
`endif

`ifdef FABRIC_AHBL
import AHBL_Types    :: *;
import AHBL_Defs     :: *;
`endif

import ISA_Decls     :: *;

`ifdef INCLUDE_TANDEM_VERIF
import TV_Info       :: *;
`endif

import GPR_RegFile   :: *;
`ifdef ISA_F
import FPR_RegFile   :: *;
`endif
`ifdef MIN_CSR
import CSR_RegFile_Min :: *;
`else
import CSR_RegFile_MSU :: *;
`endif
import CPU_Globals   :: *;
import CPU_IFC       :: *;

`ifdef ISA_C
// 'C' extension (16b compressed instructions)
import CPU_Fetch_C   :: *;
import CPU_Decode_C  :: *;
`endif

import EX_ALU_functions :: *;

import Near_Mem_IFC :: *;    // Caches or TCM

import MMU_Cache_Common :: *;

`ifdef Near_Mem_Caches
import Near_Mem_Caches  :: *;
`endif

`ifdef Near_Mem_TCM
import Near_Mem_TCM :: *;
`endif

`ifdef ISA_M
import RISCV_MBox :: *;
`endif

`ifdef SHIFT_SERIAL
import Shifter_IFC :: *;
import Shifter_Box :: *;
`endif

`ifdef ISA_F
import FBox_Top    :: *;
import FBox_Core   :: *;   // For fv_nanbox function
`endif

`ifdef INCLUDE_GDB_CONTROL
import DM_Common        :: *;
import Debug_Interfaces :: *;
`endif

import DM_CPU_Req_Rsp    :: *;   // for SB_Sys_Req

import Core_Map :: *;    // Only for pc_reset_value

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
   , CPU_EXEC1            // Normal operation: Execution stage1
   , CPU_EXEC2            // Normal operation: Execution stage2 (retirement for RV32I)
   , CPU_LD_COMPLETION    // Normal operation: Execution stage3: LD retire
   , CPU_ST_COMPLETION    // Normal operation: Execution stage3: ST retire
   , CPU_CSRR_W_COMPLETION// Normal operation: Execution stage3: CSRR_W retire
   , CPU_CSRR_S_C_COMPLETION// Normal operation: Execution stage3: CSRR_S_C retire
`ifdef ISA_A
   , CPU_AMO_COMPLETION   // Normal operation: Execution stage3: AMO completion in NM
   , CPU_AMO_COMPLETION2  // Normal operation: Execution stage4: AMO retire?
`endif
`ifdef ISA_M
   , CPU_M_COMPLETION     // Normal operation: Execution stage3: M retire
`endif
`ifdef ISA_F
   , CPU_FD_COMPLETION    // Normal operation: Execution stage3: FD retire
`endif
`ifdef SHIFT_SERIAL
   , CPU_SH_COMPLETION    // Normal operation: Execution stage3: Shift retire
`endif
   , CPU_TRAP
   , CPU_RESTART_TRAP     // Restart (fetch) after a trap (breaks timing path)
   , CPU_BREAK            // Prepare to BREAK
   , CPU_INTERRUPT_PENDING// Take interrupt
   , CPU_RESTART_EXT_INT  // Restart (fetch) after an ext interrupt
`ifdef ISA_PRIV_S
   , CPU_SFENCE_VMA_COMPLETION// Normal operation: Execution stage2: SFENCE.VM
`endif
   , CPU_WFI_PAUSED        // On WFI pause
} CPU_State deriving (Eq, Bits, FShow);

// ----------------

function Bool fn_is_running (CPU_State  cpu_state);
   return (   (cpu_state != CPU_RESET1)
           && (cpu_state != CPU_RESET2)
`ifdef INCLUDE_GDB_CONTROL
           && (cpu_state != CPU_GDB_PAUSING)
           && (cpu_state != CPU_DEBUG_MODE)
`endif
           );
endfunction

// ================================================================
// Magritte RISC-V CPU module implementation

(* synthesize *)
module mkCPU (CPU_IFC);

   // ----------------
   // System address map and pc reset value
   Core_Map_IFC  addr_map  <- mkCore_Map;

   // ----------------
   // General purpose registers, floating point registers and CSRs
   GPR_RegFile_IFC  gpr_regfile  <- mkGPR_RegFile;
`ifdef ISA_F
   FPR_RegFile_IFC  fpr_regfile  <- mkFPR_RegFile;
`endif
   CSR_RegFile_IFC  csr_regfile  <- mkCSR_RegFile;

   // ----------------
   // Integer multiply/divide box

`ifdef ISA_M
   RISCV_MBox_IFC mbox <- mkRISCV_MBox;
`endif

   // ----------------
   // Floating point box

`ifdef ISA_F
   FBox_Top_IFC fbox <- mkFBox_Top (0);
`endif

   // ----------------
   // Serial Shifter box
`ifdef SHIFT_SERIAL
`ifdef SHIFT_LOGARITHMIC
   Shifter_Box_IFC sbox <- mkLog_Shifter_Box;
`else
   Shifter_Box_IFC sbox <- mkShifter_Box;
`endif
`endif

   // ----------------
   // Near mem (caches or TCM, for example, for instruction memory and data memory)
   Near_Mem_IFC  near_mem <- mkNear_Mem;

   // Take imem as-is from near_mem, or use wrapper for 'C' extension
`ifdef ISA_C
   // XXX Revisit after Near_Mem Change
   let imem_c <- mkCPU_Fetch_C (near_mem.imem);
   let imem = imem_c.imem;
`else
   let imem = near_mem.imem;
`endif

   // ----------------
   // Re-initialize module: requests and responses (at any time, not just power-up)

   FIFOF #(Bool)  f_reset_reqs <- mkFIFOF1;
   FIFOF #(Bool)  f_reset_rsps <- mkFIFOF1;

   // ----------------
   // Major CPU states
   Reg #(CPU_State)  rg_state    <- mkReg (CPU_RESET1);
`ifndef MIN_CSR
   Reg #(Priv_Mode)  rg_cur_priv <- mkReg (m_Priv_Mode);
`endif
   Reg #(Addr)       rg_pc       <- mkRegU;
   // Reg #(Maybe#(Exc_Code)) rg_exc<- mkReg (tagged Invalid);

   // Information used by the COMPLETION states
   // Reg #(Completion_Info) rg_completion_info <- mkRegU;
   Reg #(EXEC1_Inputs) rg_exec1_inputs <- mkRegU;
   Reg #(ALU_Outputs) rg_alu_outputs <- mkRegU;
   Reg #(Bool) rg_csr_permitted <- mkReg (True);

   // Info communicated to rl_trap from previous rules that detect the trap.
   Reg #(Pipe_Trap_Info) rg_trap_info <- mkRegU;

   // Save resume-PC across 2-phase instructions (like FENCE.I) that
   // may change imem outputs (like 'pc', 'is_i32_not_i16', etc.)

   // Reg #(WordXL) rg_pc_resume <- mkRegU;


   // ----------------------------------------------------------------
   // Some continuous values derived from the above modules

   // ----------------
   // Commonly used CSR values
   let mcycle   = csr_regfile.read_csr_mcycle;
`ifdef EVAL
   let cyc_exp  = (mcycle [36:28] == 9'h1BF); // ~ 20 mins at 100 MHz
`endif
   let misa     = csr_regfile.read_misa;
`ifndef MIN_CSR
   let mstatus  = csr_regfile.read_mstatus;
`endif
   let minstret = csr_regfile.read_csr_minstret;

`ifndef MIN_CSR
   // ----------------
   // Virtual-memory memory-access parameters

   Priv_Mode  mem_priv = ((mstatus [17] == 1'b1) ? mstatus [12:11] : rg_cur_priv);

   // MSTATUS.MXR and SSTATUS.SUM for Virtual Memory access control
   Bit #(1) mstatus_MXR = mstatus [19];
`ifdef ISA_PRIV_S
   Bit #(1) sstatus_SUM = (csr_regfile.read_sstatus) [18];
`else
   Bit #(1) sstatus_SUM = 0;
`endif

   WordXL  satp = csr_regfile.read_satp;
`endif

   // ----------------
   // Interrupt pending based on current priv, mstatus.ie, mie and mip registers
`ifdef MIN_CSR
   Bool interrupt_pending = (   isValid (csr_regfile.interrupt_pending));
`else
   Bool interrupt_pending = (   isValid (csr_regfile.interrupt_pending (rg_cur_priv))
                             || csr_regfile.nmi_pending);
`endif

   // ----------------
   // For local debugging

`ifdef SYNTHESIS
   // Current verbosity - meaningless on FPGA
   Bit #(2)  cur_verbosity = 0;
`else
   // Verbosity: 0=quiet; 1=instruction trace; 2=more detail
   Reg #(Bit #(2))  cfg_verbosity <- mkConfigReg (0);

   // Current verbosity, taking into account log delay
   Bit #(2)  cur_verbosity = cfg_verbosity;
`endif

   // ----------------------------------------------------------------
   // Interaction with external Debug Module

`ifdef INCLUDE_GDB_CONTROL

   // Debugger run-control
   FIFOF #(Bool)  f_run_halt_reqs <- mkFIFOF;
   FIFOF #(Bool)  f_run_halt_rsps <- mkFIFOF;

   // Stop-request from debugger (e.g., GDB ^C or Dsharp 'stop')
   Reg #(Bool)  rg_stop_req <- mkReg (False);      // stop/halt request
   Reg #(Bool)  rg_step_req <- mkReg (False);      // step-request from dcsr.step

   // Debugger GPR read/write request/response
   FIFOF #(DM_CPU_Req #(5,  XLEN)) f_gpr_reqs <- mkFIFOF1;
   FIFOF #(DM_CPU_Rsp #(XLEN))     f_gpr_rsps <- mkFIFOF1;

`ifdef ISA_F
   // Debugger FPR read/write request/response
   FIFOF #(DM_CPU_Req #(5,  FLEN)) f_fpr_reqs <- mkFIFOF1;
   FIFOF #(DM_CPU_Rsp #(FLEN))     f_fpr_rsps <- mkFIFOF1;
`endif

   // Debugger CSR read/write request/response
   // XXX Consider shrinking when using MIN_CSR
   FIFOF #(DM_CPU_Req #(12, XLEN)) f_csr_reqs <- mkFIFOF1;
   FIFOF #(DM_CPU_Rsp #(XLEN))     f_csr_rsps <- mkFIFOF1;

   // Halt requests (interrupts, debugger stop-request, or dcsr.step step-request)
   // We set this flag on an instruction Fetch and handle it on the next ifetch
   Reg #(Bool)  rg_halt <- mkReg (False);

`else
`ifdef TCM_LOADER
   Reg #(Bool)  rg_stop_req <- mkReg (False);      // stop/halt request
`endif
`endif

   // ----------------------------------------------------------------
   // Tandem Verification

`ifdef INCLUDE_TANDEM_VERIF
   // XXX Do we need a deeper FIFO? Should it be a BRAMFIFO?
   FIFOF #(Trace_Data) f_trace_data  <- mkFIFOF;

   // State for deciding if a MIP update needs to be sent into the trace file
   Reg #(WordXL) rg_prev_mip <- mkReg (0);
`endif

   function Bool mip_cmd_needed ();
`ifdef INCLUDE_TANDEM_VERIF
      // If the MTIP, MSIP, or xEIP bits of MIP have changed, then send a MIP update
      WordXL new_mip = csr_regfile.csr_mip_read;
      Bool mip_has_changed = (new_mip != rg_prev_mip);
      return mip_has_changed;
`else
      return False;
`endif
   endfunction: mip_cmd_needed

   // ================================================================
   // Debugging: print instruction trace info.
   // Memory store update only for RV32, not generalized for RV64
   function Action fa_emit_instr_trace (Bit #(64) instret1
      , WordXL pc1
      , Instr instr1
      , Maybe #(Tuple2 #(RegName, WordXL)) gpr_update
      , Maybe #(Tuple2 #(Addr, Bit #(32))) mem_update
`ifndef MIN_CSR
      , Priv_Mode priv1
`endif
      );
      action
      $write ("(instret:%06d) ", instret1);
      $write ("(PC:0x%08h) ", pc1);
      $write ("(instr:0x%08h) ", instr1);
      if (isValid (gpr_update)) begin
         match {.rd, .rdval} = gpr_update.Valid;
         $write ("(GPR[%02d]<-0x%08h) ", rd, rdval);
      end
      else begin
         $write ("                      ");
      end

      // Incomplete implementation. Does not take into account
      // f3 field to show actual bytes updated.
      if (isValid (mem_update)) begin
         match {.addr, .data} = mem_update.Valid;
         $write ("(MEM[0x%08h]<-0x%08h) ", addr, data);
      end

      else begin
         $write ("                              ");
      end
`ifndef MIN_CSR
      $write ("(priv:%06d)", priv1);
`endif
      $write ("\n");
      endaction
   endfunction

`ifndef SYNTHESIS
   // ----------------
   // CPI measurement in each 'run' (from Debug Mode pause to Debug Mode pause)

   Reg #(Bit #(64))  rg_start_CPI_cycles <- mkRegU;
   Reg #(Bit #(64))  rg_start_CPI_instrs <- mkRegU;

   function Action fa_report_CPI;
      action
         Bit #(64) delta_CPI_cycles = mcycle - rg_start_CPI_cycles;
         Bit #(64) delta_CPI_instrs = minstret - rg_start_CPI_instrs;

         // Make delta_CPI_instrs at least 1, to avoid divide-by-zero
         if (delta_CPI_instrs == 0)
            delta_CPI_instrs = delta_CPI_instrs + 1;

         // Report CPI to 1 decimal place.
         let x = (delta_CPI_cycles * 10) / delta_CPI_instrs;
         let cpi     = x / 10;
         let cpifrac = x % 10;
         $display ("CPI: %0d.%0d = (%0d/%0d) since last 'continue'",
                   cpi, cpifrac, delta_CPI_cycles, delta_CPI_instrs);
      endaction
   endfunction
`endif

   // ================================================================
   // Feed a new PC into IMem (to do an instruction fetch).
   // Set rg_halt on debugger stop request or dcsr.step step request
`ifdef MIN_CSR
   function Action fa_start_ifetch (Word next_pc);
`else
   function Action fa_start_ifetch (Word next_pc, Priv_Mode priv);
`endif
      action
         // Save the PC because the IMem no longer does
         rg_pc <= next_pc;

`ifdef INCLUDE_GDB_CONTROL
         // Set rg_halt if requested by GDB (stop req, step req)
         Bool do_halt = False;

         // Debugger stop-request
         if ((! do_halt) && rg_stop_req && (cur_verbosity != 0))
            $display ("    CPU.fa_start_ifetch: halting due to stop_req: PC = 0x%08h",
                      next_pc);

         do_halt = (do_halt || rg_stop_req);

         // dcsr.step step-request
         if ((! do_halt) && rg_step_req && (cur_verbosity != 0))
            $display (" CPU.fa_start_ifetch: halting due to step req: PC = 0x%08h",
                      next_pc);
         do_halt = (do_halt || rg_step_req);

         // If not halting now, and dcsr.step=1, set rg_step_req to cause a stop
         // at next fetch
         if ((! do_halt) && (csr_regfile.read_dcsr_step)) begin
            rg_step_req <= True;
            if (cur_verbosity != 0)
               $display ("    CPU.fa_start_ifetch: dcsr.step=1; will stop at next fetch");
         end

         if (do_halt) begin
            rg_halt <= True;
            if (cur_verbosity > 1)
               $display ("    CPU.fa_start_ifetch: rg_halt <= True");
         end

         // If we are halting, the fetch will be issued when continuing from the
         // stopped state. This adds logic to the IMem request path (to the EN
         // signal), but only when built with GDB.
         if (!do_halt)
`endif
            // Initiate the fetch
            imem.req (next_pc);
      endaction
   endfunction

   // ================================================================
   // Actions to restart from Debug Mode (e.g., GDB 'continue' after a breakpoint)
   // We re-initialize CPI_instrs and CPI_cycles.

   function Action fa_restart (Addr resume_pc);
      action
`ifdef MIN_CSR
         fa_start_ifetch (resume_pc);
`else
         fa_start_ifetch (resume_pc, rg_cur_priv);
`endif
         rg_state <= CPU_RUNNING;

`ifdef INCLUDE_GDB_CONTROL
         if (rg_state != CPU_RESET2) begin
            // Did not get here from reset
            // Notify debugger that we've started running
            f_run_halt_rsps.enq (True);
         end
`endif
`ifndef SYNTHESIS
         rg_start_CPI_cycles <= mcycle;
         rg_start_CPI_instrs <= minstret;
`endif

         if (cur_verbosity != 0)
            $display ("    fa_restart: RUNNING with PC = 0x%0h", resume_pc);
      endaction
   endfunction

   // ================================================================
   // Actions to move to a trap state
   function Action fa_take_trap (String trap_reason, Addr epc, Exc_Code exc, Addr tval);
      action
         let trap_info = Pipe_Trap_Info {epc: epc, exc_code: exc, tval: tval};
         rg_trap_info <= trap_info;
         rg_state <= CPU_TRAP;

         // Debug
         if (cur_verbosity > 1) begin
            $display ( "    %s: ", trap_reason, fshow (trap_info));
         end
      endaction
   endfunction

   // ----------------------------------------------------------------
   // Top-level ALU function

   function Action fa_ALU (ALU_Inputs inputs);
      action
      CPU_State next_state = CPU_EXEC2;

      let alu_outputs = alu_outputs_base;
      alu_outputs.rd  = instr_rd (inputs.instr);

      let funct3      = instr_funct3 (inputs.instr);

      if (inputs.ucontrol.opcode.is_op_BRANCH)
         alu_outputs = fv_BRANCH (inputs);

      else if (inputs.ucontrol.opcode.is_op_JAL)
         alu_outputs = fv_JAL (inputs);

      else if (inputs.ucontrol.opcode.is_op_JALR)
         alu_outputs = fv_JALR (inputs);

`ifdef ISA_M
      // OP 'M' ops MUL/ MULH/ MULHSU/ MULHU/ DIV/ DIVU/ REM/ REMU
      else if (   inputs.ucontrol.opcode.is_op_OP
               && inputs.ucontrol.f7.is_f7_MUL_DIV_REM)
         begin
            // Will be executed in MBox in next stage
            alu_outputs.op_stage2 = OP_Stage2_M;
            alu_outputs.val1      = inputs.rs1_val;
            alu_outputs.val2      = inputs.rs2_val;

`ifdef INCLUDE_TANDEM_VERIF
            // Normal trace output (if no trap)
            alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
                                                   fv_trace_isize (inputs),
                                                   fv_trace_instr (inputs),
                                                   instr_rd (inputs.instr),
                                                   ?);
`endif
         end

`ifdef RV64
      // OP 'M' ops MULW/ DIVW/ DIVUW/ REMW/ REMUW
      else if (   inputs.ucontrol.opcode.is_op_OP_32
               && inputs.ucontrol.f7.is_f7_MUL_DIV_REM)
         begin
            // Will be executed in MBox in next stage
            alu_outputs.op_stage2 = OP_Stage2_M;
            alu_outputs.rd        = inputs.decoded_instr.rd;
            alu_outputs.val1      = inputs.rs1_val;
            alu_outputs.val2      = inputs.rs2_val;

`ifdef INCLUDE_TANDEM_VERIF
            // Normal trace output (if no trap)
            alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
                                                   fv_trace_isize (inputs),
                                                   fv_trace_instr (inputs),
                                                   instr_rd (inputs.instr),
                                                   ?);
`endif
         end
`endif
`endif

      // OP_IMM and OP (shifts)
      else if (   (   (inputs.ucontrol.opcode.is_op_OP_IMM)
                   || (inputs.ucontrol.opcode.is_op_OP))
               && (   (inputs.ucontrol.f3.is_f3_SLL)
                   || (inputs.ucontrol.f3.is_f3_SRx))) begin
         alu_outputs = fv_OP_and_OP_IMM_shifts (inputs);
`ifdef SHIFT_SERIAL
         // Dispatch to serial shifter if the instruction is good
         if (alu_outputs.control != CONTROL_TRAP) begin
            next_state = CPU_SH_COMPLETION;
            sbox.req (!inputs.ucontrol.f3.is_f3_SLL, alu_outputs.val1, alu_outputs.val2);
         end
`endif
      end

      // Remaining OP_IMM and OP (excluding shifts and 'M' ops MUL/DIV/REM)
      else if (   (inputs.ucontrol.opcode.is_op_OP_IMM)
               || (inputs.ucontrol.opcode.is_op_OP))
         alu_outputs = fv_OP_and_OP_IMM (inputs);

`ifdef RV64
      else if (inputs.ucontrol.opcode.is_op_OP_IMM_32)
         alu_outputs = fv_OP_IMM_32 (inputs);

      // Remaining op_OP_32 (excluding 'M' ops)
      else if (inputs.ucontrol.opcode.is_op_OP_32)
         alu_outputs = fv_OP_32 (inputs);
`endif

      else if (inputs.ucontrol.opcode.is_op_LUI)
         alu_outputs = fv_LUI (inputs);

      else if (inputs.ucontrol.opcode.is_op_AUIPC)
         alu_outputs = fv_AUIPC (inputs);

      else if (inputs.ucontrol.opcode.is_op_LOAD) begin
         alu_outputs = fv_LD (inputs);
         next_state = CPU_LD_COMPLETION;

         // Initiate LD and go to LD_COMPLETION state
         near_mem.dmem.req (
              CACHE_LD
            , funct3
`ifdef ISA_A
            , amo_funct7   : amo_funct7
`endif
            , alu_outputs.addr
            , ?   // (irrelevant)
`ifdef ISA_PRIV_S
            , priv         : mem_priv
            , sstatus_SUM  : sstatus_SUM
            , mstatus_MXR  : mstatus_MXR
            , satp         : satp
`endif
         );
      end

      else if (inputs.ucontrol.opcode.is_op_STORE) begin
         alu_outputs = fv_ST (inputs);
         next_state = CPU_ST_COMPLETION;
         // Prepare the store value
`ifdef RV64
         Bit# (64) wdata_from_gpr = alu_outputs.val2;
`else
         Bit# (32) wdata_from_gpr = (alu_outputs.val2);
`endif

`ifdef ISA_F
`ifdef ISA_D
         Bit# (64) wdata_from_fpr = alu_outputs.fval2;
`else
         Bit# (32) wdata_from_fpr = (alu_outputs.fval2);
`endif
`endif

         // Currently the 32-bit NM does not support RV64 and ISA-D functionality.
         near_mem.dmem.req (
              CACHE_ST
            , funct3
`ifdef ISA_A
            , amo_funct7   : amo_funct7
`endif
            , alu_outputs.addr
`ifdef ISA_F
            , (alu_outputs.rs_frm_fpr ? wdata_from_fpr : wdata_from_gpr)
`else
            , wdata_from_gpr
`endif
`ifdef ISA_PRIV_S
            , priv         : mem_priv
            , sstatus_SUM  : sstatus_SUM
            , mstatus_MXR  : mstatus_MXR
            , satp         : satp
`endif
         );
      end

      else if (inputs.ucontrol.opcode.is_op_MISC_MEM) begin
         alu_outputs = fv_MISC_MEM (inputs);
      end

      else if (inputs.ucontrol.opcode.is_op_SYSTEM)
         alu_outputs = fv_SYSTEM (inputs);

   `ifdef ISA_A
      else if (inputs.ucontrol.opcode.is_op_AMO) begin
         alu_outputs = fv_AMO (inputs);
      end
   `endif

   `ifdef ISA_F
      else if (   (inputs.ucontrol.opcode.is_op_LOAD_FP))
         alu_outputs = fv_LD (inputs);

      else if (   (inputs.ucontrol.opcode.is_op_STORE_FP))
         alu_outputs = fv_ST (inputs);

      else if (   (inputs.ucontrol.opcode.is_op_FP)
               || (inputs.ucontrol.opcode.is_op_FMADD)
               || (inputs.ucontrol.opcode.is_op_FMSUB)
               || (inputs.ucontrol.opcode.is_op_FNMSUB)
               || (inputs.ucontrol.opcode.is_op_FNMADD))
         alu_outputs = fv_FP (inputs);
   `endif

      else begin
         alu_outputs.control = CONTROL_TRAP;

   `ifdef INCLUDE_TANDEM_VERIF
         // Normal trace output (if no trap)
         alu_outputs.trace_data = mkTrace_TRAP (fall_through_pc (inputs),
                                                fv_trace_isize (inputs),
                                                fv_trace_instr (inputs),
                                                ?,
                                                ?,
                                                ?,
                                                ?,
                                                ?);
   `endif
      end

      rg_state <= next_state;
      rg_alu_outputs <= alu_outputs;
      endaction
   endfunction

   // ================================================================
   // Reset

   rule rl_reset_start (rg_state == CPU_RESET1);
      let req <- pop (f_reset_reqs);

      $display ("================================================================");
      $write ("CPU: Bluespec  RISC-V  Low Footprint Core v1.3");
      if (rv_version == RV32) $display (" (RV32)");
      else $display (" (RV64)");
      $display ("Simple FSM CPU, i.e., not pipelined");
      $display ("Copyright (c) 2018-2022 Bluespec, Inc. All Rights Reserved.");
      $display ("================================================================");

`ifdef ISA_C
      imem_c.reset;
`endif
      near_mem.server_reset.request.put (?);

      gpr_regfile.server_reset.request.put (?);
`ifdef ISA_F
      fpr_regfile.server_reset.request.put (?);
      fbox.server_reset.request.put (?);
`endif
      csr_regfile.server_reset.request.put (?);

`ifdef SHIFT_SERIAL
      sbox.server_reset.request.put (?);
`endif

`ifndef MIN_CSR
      rg_cur_priv <= m_Priv_Mode;
`endif
      rg_state    <= CPU_RESET2;

      if (cur_verbosity != 0)
         $display ("%06d:[D]:%m.rl_reset_start", cur_cycle);

`ifdef INCLUDE_GDB_CONTROL
      rg_halt     <= False;
      rg_step_req <= False;

      // If the debugger wants us to come up halted, the stop_req
      // needs to record that intent. req is True => the CPU should
      // come up running. Based on this flag we figure out how to
      // exit reset in the next state
      rg_stop_req <= !req;

      f_run_halt_reqs.clear;
      f_run_halt_rsps.clear;
      f_csr_reqs.clear;
      f_csr_rsps.clear;
      f_gpr_reqs.clear;
      f_gpr_rsps.clear;
`ifdef ISA_F
      f_fpr_reqs.clear;
      f_fpr_rsps.clear;
`endif

`else
`ifdef TCM_LOADER
      // If the loader wants us to come up halted, the stop_req
      // needs to record that intent. req is True => the CPU should
      // come up running. Based on this flag we figure out how to
      // exit reset in the next state
      rg_stop_req <= !req;
`endif
`endif

`ifdef INCLUDE_TANDEM_VERIF
      let trace_data = mkTrace_RESET;
      f_trace_data.enq (trace_data);

      rg_prev_mip <= 0;
`endif
   endrule: rl_reset_start

   // ----------------

   rule rl_reset_complete (rg_state == CPU_RESET2);
      let ack_nm <- near_mem.server_reset.response.get;
      let ack_gpr <- gpr_regfile.server_reset.response.get;
`ifdef ISA_F
      let ack_fpr <- fpr_regfile.server_reset.response.get;
      let ack_fbox <- fbox.server_reset.response.get;
`endif
      let ack_csr <- csr_regfile.server_reset.response.get;

`ifdef SHIFT_SERIAL
      let ack_sbox <- sbox.server_reset.response.get;
`endif

      if (cur_verbosity != 0)
         $display ("%06d:[D]:%m.rl_reset_complete", cur_cycle);

`ifdef INCLUDE_GDB_CONTROL
`ifdef MIN_CSR
      csr_regfile.write_dcsr_cause_priv (DCSR_CAUSE_HALTREQ, m_Priv_Mode);
`else
      csr_regfile.write_dcsr_cause_priv (DCSR_CAUSE_HALTREQ, rg_cur_priv);
`endif
      // Response to debugger indicates run/hlt state
      f_reset_rsps.enq (!rg_stop_req);
      if (rg_stop_req) begin
         // The CPU should come up halted
         rg_stop_req <= False;
         rg_state <= CPU_DEBUG_MODE;

         if (cur_verbosity != 0)
            $display ("    CPU entering DEBUG_MODE");
      end

      // The CPU should come up running
      else begin
         WordXL dpc = truncate (addr_map.m_pc_reset_value);
         fa_restart (dpc);    // sets rg_state <= CPU_RUNNING
      end
`else
`ifdef TCM_LOADER
      // Response to debugger indicates run/hlt state
      f_reset_rsps.enq (!rg_stop_req);

      if (rg_stop_req) begin
         // The CPU should come up halted
         rg_stop_req <= False;
         rg_state <= CPU_DEBUG_MODE;

         if (cur_verbosity != 0)
            $display ("    CPU entering DEBUG_MODE (TCM Load)");
      end

      else begin
         WordXL dpc = truncate (addr_map.m_pc_reset_value);
         fa_restart (dpc);    // sets rg_state <= CPU_RUNNING
      end
`else
      f_reset_rsps.enq (True);

      WordXL dpc = truncate (addr_map.m_pc_reset_value);
      fa_restart (dpc);       // sets rg_state <= CPU_RUNNING
`endif
`endif
   endrule: rl_reset_complete

   // ================================================================
   // Main run-loop

   function Action fa_finish_instr (
        Addr                                 next_pc
      , Maybe #(Tuple2 #(RegName, WordXL))   gpr_update
      , Maybe #(Tuple2 #(Addr, Bit #(32)))   mem_update
`ifndef MIN_CSR
      , Priv_Mode                            new_priv
`endif
   );
      action
         fa_start_ifetch (next_pc);

         // Accounting
         csr_regfile.csr_minstret_incr;

         // Debug
         if (cur_verbosity >= 1)
            fa_emit_instr_trace (
                 minstret
               , rg_pc
`ifdef ISA_C
               , (rg_exec1_inputs.is_i32_not_i16 ? rg_exec1_inputs.instr
                                                 : extend (rg_exec1_inputs.instr_C))
`else
               , rg_exec1_inputs.instr
`endif
               , gpr_update
               , mem_update
`ifndef MIN_CSR
               , rg_cur_priv
`endif
            );

      endaction
   endfunction

   // ================================================================
   // Main loop: result available from IMEM.
   // 1: Check if there is an except -- trap
   // 2: Check if there ia a pending interrupt. Jump to interrupt handling state
   // 3: Normal operation: Decode. Register read request.
   rule rl_run (
         (rg_state == CPU_RUNNING)
      && (!f_reset_reqs.notEmpty)
`ifdef EVAL
      && (!cyc_exp)
`endif
`ifdef INCLUDE_GDB_CONTROL
      && (! rg_halt)
`endif
   );
      match {.instr, .irsp_exc} <- imem.instr ();
      // Trap
      // XXX : Review. Using the PC as the TVAL
      if (isValid (irsp_exc))
         fa_take_trap ("   IMem: Trap", rg_pc, irsp_exc.Valid, rg_pc);

      // Interrupt pending
      else if (interrupt_pending) begin
         rg_state <= CPU_INTERRUPT_PENDING;
         if (cur_verbosity > 2)
            $display ("%06d:[D]:%m.rl_run: Interrupt pending", cur_cycle);
      end

      // Normal operation
      else begin
         // ----------------
         // Current instruction coming out of IMem, and its fields etc.

`ifdef ISA_C
         let is_i32_not_i16 = is_32b_instr (instr);
         // ---- If a Compressed instruction (in lsbs of IMem output), decode it
         Instr_C instr_C = instr [15:0];
         if (! is_i32_not_i16)
            instr = fv_decode_C (misa, misa.mxl, instr_C);
`endif

         let decoded_ucontrol = fv_decode (instr);

         let rd               = instr_rd (instr);
         let csr              = instr_csr (instr);

         // ================================================================
         // Combinational paths from decoded_instr through regfiles, ALU, etc.

         // Register rs1 read
         let rs1     = instr_rs1 (instr);
         let rs1_val = gpr_regfile.read_rs1 (rs1);

         // Register rs2 read
         let rs2     = instr_rs2 (instr);
         let rs2_val = gpr_regfile.read_rs2 (rs2);

`ifdef ISA_F
         // FP Register rs1 read
         let frs1_val = fpr_regfile.read_rs1 (rs1);

         // FP Register rs2 read
         let frs2_val = fpr_regfile.read_rs2 (rs2);

         // FP Register rs3 read
         let rs3 = instr_rs3 (instr);
         let frs3_val = fpr_regfile.read_rs3 (rs3);
`endif

         // ----------------
         // ALU inputs

         // Set up inputs for the next stage
         let exec1_inputs = EXEC1_Inputs {
              instr           : instr
`ifdef ISA_C
            , is_i32_not_i16  : is_i32_not_i16
            , instr_C         : instr_C
`endif
            , ucontrol        : decoded_ucontrol
            , rs1_val         : rs1_val
            , rs2_val         : rs2_val
`ifdef ISA_F
            , frs1_val        : frs1_val
            , frs2_val        : frs2_val
            , frs3_val        : frs3_val
            , frm             : csr_regfile.read_frm
`endif
         };

         // save state for the EXEC stage and beyond
         rg_exec1_inputs <= exec1_inputs;
         rg_state <= CPU_EXEC1;

         // compute next pc -- moved here to allow the output
         // one more cycle to settle
         /*
`ifdef ISA_C
         let next_pc = rg_pc + (is_i32_not_i16 ? 4 : 2);
`else
         let next_pc = rg_pc + 4;
`endif
         rg_pc_resume <= next_pc;*/

         // ----------------
         // Debug
         if (cur_verbosity > 2) begin
            $display ("%06d:[D]:%m.rl_run: ", cur_cycle, fshow(rg_state)
               , " (pc: 0x%08x) (instr: 0x%08x) (rs1: %0d, 0x%08x) (rs2: %0d, 0x%08x) (rd: %0d)"
               , rg_pc, instr, rs1, rs1_val, rs2, rs2_val, instr_rd (instr));
            $fflush(stdout);
         end
      end
   endrule

   // ================================================================
   // Execution Stage 1. I-ALU.
   rule rl_exec1 (
         (rg_state == CPU_EXEC1)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );
      // Read the saved state ...
      let inputs = rg_exec1_inputs;

      // Prepare inputs for the ALU
      let alu_inputs = ALU_Inputs {
           pc              : rg_pc
         , instr           : inputs.instr
`ifdef ISA_C
         , is_i32_not_i16  : inputs.is_i32_not_i16
`endif
         , ucontrol        : inputs.ucontrol
         , rs1_val         : inputs.rs1_val
         , rs2_val         : inputs.rs2_val
`ifdef ISA_F
         , frs1_val        : inputs.frs1_val
         , frs2_val        : inputs.frs2_val
         , frs3_val        : inputs.frs3_val
         , frm             : inputs.frm
`endif
`ifndef MIN_CSR
         , cur_priv        : rg_cur_priv
         , mstatus         : mstatus
         , misa            : misa
`endif
      };

      // Continuous ALU outputs
      fa_ALU (alu_inputs);

      // compute next pc
      /*
`ifdef ISA_C
      let next_pc = rg_pc + (inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif
      rg_pc_resume <= next_pc; */

      // ----------------
      // Debug
      if (cur_verbosity > 1) begin
         $display ("%06d:[D]:%m.rl_exec1: ", cur_cycle, fshow(rg_state), "  ", fshow (alu_inputs));
         $fflush(stdout);
      end
   endrule


   // ================================================================
   // Execution Stage 2 (BRANCH and STAGE2_ALU complete here)
   rule rl_exec2 (
         (rg_state == CPU_EXEC2)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );
      // Read the saved state ...
      let alu_outputs = rg_alu_outputs;
      let alu_inputs  = rg_exec1_inputs;
      let instr = alu_inputs.instr;
`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      let pc = rg_pc;
      let funct3 = instr_funct3 (instr);
`ifdef ISA_A
      Bit #(7) amo_funct7 = alu_outputs.val1 [6:0];
`endif

      // ----------------
      // Debug
      Bool b = ((cur_verbosity > 0) || False );    // ((minstret % 1000000) == 0));
      if (b) begin
         if (cur_verbosity > 2) begin
            $display ("%06d:[D]:%m.rl_exec2: ", cur_cycle, fshow(rg_state), "  ", fshow (alu_outputs));
            $fflush(stdout);
         end
      end

      // ----------------------------------------------------------------
      // CONTROL_BRANCH: BEQ/BNE/BLT/BGE/BLTU/BGEU/JAL/JALR

      if (alu_outputs.control == CONTROL_BRANCH) begin
         // Writeback GPR (rd is 0 for BRANCH instrs)
         gpr_regfile.write_rd (alu_outputs.rd, alu_outputs.val1);

         // Resume execution
         rg_state <= CPU_RUNNING;

         if (cur_verbosity > 1) begin
            $display ("    CONTROL_BRANCH reg [%0d] <= 0x%08h",
                      alu_outputs.rd, alu_outputs.val1);
            $fflush(stdout);
         end

`ifndef INCLUDE_GDB_CONTROL
         // Simulation heuristic. If jumping to the same address, exit
         if (alu_outputs.addr == rg_pc) begin
            $display ("%06d:[D]:%m.rl_exec2: Tight infinite loop: pc 0x%0x"
               , cur_cycle, alu_outputs.addr);
            $finish (0);
         end
`endif
         fa_finish_instr (
              alu_outputs.addr
            , tagged Invalid
            , tagged Invalid
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );
      end

      // ----------------------------------------------------------------
      // CONTROL_STRAIGHT: ALU, LD, ST, AMO, M, FD

      else if (alu_outputs.control == CONTROL_STRAIGHT) begin
         if (alu_outputs.op_stage2 == OP_Stage2_ALU) begin
            // Writeback GPR
            gpr_regfile.write_rd (alu_outputs.rd, alu_outputs.val1);

            // Resume execution
            rg_state <= CPU_RUNNING;

            if (cur_verbosity > 1) begin
               $display ("    CONTROL_STRAIGHT, ALU: reg [%0d] <= 0x%08h; next_pc = 0x%08h",
                         alu_outputs.rd, alu_outputs.val1, next_pc);
               $fflush(stdout);
            end

            fa_finish_instr (
                 next_pc
               , tagged Valid (tuple2 (alu_outputs.rd, alu_outputs.val1))
               , tagged Invalid
`ifndef MIN_CSR
               , rg_cur_priv
`endif
            );
         end

`ifdef ISA_A
         // Atomics
         else if (alu_outputs.op_stage2 == OP_Stage2_AMO) begin
            // Initiate AMO and go to AMO_COMPLETION state
            near_mem.dmem.request.put (Near_Mem_DReq {
                 op           : CACHE_AMO
               , f3           : funct3
               , amo_funct7   : amo_funct7
               , addr         : alu_outputs.addr
               , store_value  : alu_outputs.val2
`ifdef ISA_PRIV_S
               , priv         : mem_priv
               , sstatus_SUM  : sstatus_SUM
               , mstatus_MXR  : mstatus_MXR
               , satp         : satp
`endif
            });
            rg_state <= CPU_AMO_COMPLETION;
            if (cur_verbosity > 1) begin
               $display ("    CONTROL_STRAIGHT, AMO: rd %0d addr 0x%08h, amo_funct7 = %d, amo_st_val = 0x%08h",
                         alu_outputs.rd, alu_outputs.addr, amo_funct7, alu_outputs.val2);
               $fflush(stdout);
            end
         end
`endif

`ifdef ISA_M
         // Integer Mult/Div
         else if (alu_outputs.op_stage2 == OP_Stage2_M) begin
            // Initiate M op and go to M_COMPLETION state
            Bool is_OP_not_OP_32 = (instr [3] == 1'b0);
            mbox.req (is_OP_not_OP_32,
                      funct3,
`ifdef ISA_D
`ifdef RV64
                      alu_outputs.val1,
                      alu_outputs.val2
`else
                      truncate (alu_outputs.val1),
                      truncate (alu_outputs.val2)
`endif
`else
                      alu_outputs.val1,
                      alu_outputs.val2
`endif
                      );
            rg_state <= CPU_M_COMPLETION;
            if (cur_verbosity > 1) begin
               $display ("    CONTROL_STRAIGHT, M: is_OP_not_OP_32 %d, funct3 %0h 0x%08h  0x%08h",
                         pack (is_OP_not_OP_32), funct3, alu_outputs.val1, alu_outputs.val2);
               $fflush(stdout);
            end
         end
`endif

`ifdef ISA_F
         // Floating point
         else if (alu_outputs.op_stage2 == OP_Stage2_FD) begin
            // Initiate FD op and go to FD_COMPLETION state
            // Instr fields required for decode for F/D opcodes
            let opcode = instr_opcode (instr);
            let funct7 = instr_funct7 (instr);
            let rs2    = instr_rs2    (instr);
            Bit #(64) val1 = (alu_outputs.val1_frm_gpr
                              ? extend (alu_outputs.val1)
                              : extend (alu_outputs.fval1));

            fbox.req (opcode,
                      funct7,
                      alu_outputs.rm,    // rounding_mode
                      rs2,
                      val1,
                      extend (alu_outputs.fval2),
                      extend (alu_outputs.fval3));
            rg_state <= CPU_FD_COMPLETION;
            if (cur_verbosity > 1) begin
               $display ("    CONTROL_STRAIGHT, FD: funct7 %0h 0x%08h  0x%08h  0x%08h",
                         funct7, val1, alu_outputs.fval2, alu_outputs.fval3);
               $fflush(stdout);
            end
         end
`endif

         else begin
            // Note: this is not for illegal instructions, which are handled as traps (see below)
            $display ("%06d:[E]:%m.rl_run: Unrecognized op_stage2", cur_cycle);
            $display ("    ", fshow (alu_outputs));
            $finish (1);
         end
      end

      // ----------------------------------------------------------------
      // CSRRW, CSRRS, CSRRC

      else if (   (alu_outputs.control == CONTROL_CSRR_W)
               || (alu_outputs.control == CONTROL_CSRR_S_or_C)) begin
         let csr_addr         = instr_csr    (instr);
         let rs1_val          = alu_outputs.val1;

         // CSRR_S_or_C only reads, does not write CSR, if rs1_val == 0. CSRR_W always writes.
         Bool read_not_write  = (alu_outputs.control == CONTROL_CSRR_S_or_C) && (rs1_val == 0);
`ifdef MIN_CSR
         Bool permitted = csr_regfile.access_permitted (csr_addr, read_not_write);
`else
         Bool permitted = csr_regfile.access_permitted (rg_cur_priv, csr_addr, read_not_write);
`endif

         rg_csr_permitted <= permitted;
         rg_state <= (alu_outputs.control == CONTROL_CSRR_W) ? CPU_CSRR_W_COMPLETION
                                                             : CPU_CSRR_S_C_COMPLETION;
      end 

      // ----------------------------------------------------------------
      // MRET/SRET/URET

      else if (   (alu_outputs.control == CONTROL_MRET)
`ifdef ISA_PRIV_S
               || (alu_outputs.control == CONTROL_SRET)
`endif
`ifdef ISA_PRIV_U
               || (alu_outputs.control == CONTROL_URET)
`endif
      ) begin
`ifdef ISA_PRIV_U
`ifdef ISA_PRIV_S
         // MUS mode
         Vector #(3, Bool) sels = newVector;
         Vector #(3, Priv_Mode) privs = newVector;
         sels[0] = (alu_outputs.control == CONTROL_MRET); privs[0] = m_Priv_Mode;
         sels[1] = (alu_outputs.control == CONTROL_URET); privs[1] = u_Priv_Mode;
         sels[2] = (alu_outputs.control == CONTROL_SRET); privs[2] = s_Priv_Mode;
         Priv_Mode from_priv = fv_and_or_mux (sels, privs);
`else
         // MU mode
         Priv_Mode from_priv = (alu_outputs.control == CONTROL_MRET) ? m_Priv_Mode 
                                                                     : u_Priv_Mode;
`endif
`else
`ifdef ISA_PRIV_S
         // MS mode
         Priv_Mode from_priv = (alu_outputs.control == CONTROL_MRET) ? m_Priv_Mode
                                                                     : s_Priv_Mode;
`else
         // M mode
         Priv_Mode from_priv = m_Priv_Mode;
`endif
`endif
`ifdef MIN_CSR
         let new_pc <- csr_regfile.csr_ret_actions;
`else
         match { .new_pc, .new_priv, .new_mstatus } <- csr_regfile.csr_ret_actions (
            from_priv);
         rg_cur_priv <= new_priv;
`endif

         // Resume execution
         rg_state <= CPU_RUNNING;

         // Debug
         if (cur_verbosity > 1) begin
`ifdef MIN_CSR
            $display ("    xRET: next_pc 0x%0h ", new_pc);
`else
            $display ("    xRET: mstatus 0x%08h  next_pc 0x%0h  new_mstatus = 0x%0h  new_priv %0d"
               , mstatus, new_pc, new_mstatus, new_priv);
`endif
            $fflush(stdout);
         end

         // Redirect PC
         fa_finish_instr (
              new_pc
            , tagged Invalid
            , tagged Invalid
`ifndef MIN_CSR
            , new_priv
`endif
         );
      end

      // ----------------------------------------------------------------
      // FENCE/FENCE_I

      else if (   (alu_outputs.control == CONTROL_FENCE)
               || (alu_outputs.control == CONTROL_FENCE_I)) begin
         // FENCE and FENCE.I ops treated as NOP by this CPU
         fa_finish_instr (
              next_pc
            , tagged Invalid
            , tagged Invalid
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );

      // Resume pipe
      rg_state <= CPU_RUNNING;


         if (cur_verbosity > 1) begin
            $display ("    CONTROL_FENCE_I/CONTROL_FENCE");
            $fflush(stdout);
         end
      end

      // ----------------------------------------------------------------
      // SFENCE_VMA

`ifdef ISA_PRIV_S
      else if (alu_outputs.control == CONTROL_SFENCE_VMA) begin
         near_mem.sfence_vma_server.request.put (?);
         rg_state <= CPU_SFENCE_VMA_COMPLETION;

         if (cur_verbosity > 1) begin
            $display ("    CONTROL_SFENCE_VMA");
            $fflush(stdout);
         end
      end
`endif

      // ----------------------------------------------------------------
      // WFI

      else if (alu_outputs.control == CONTROL_WFI) begin
         rg_state <= CPU_WFI_PAUSED;

         // Debug
         if (cur_verbosity > 1) begin
            $display ("    CONTROL_WFI");
            $fflush(stdout);
         end
      end

      // ----------------------------------------------------------------
      // TRAP

      else if (alu_outputs.control == CONTROL_TRAP) begin
         // Compute MTVAL in case of traps
         let tval = 0;
         if (alu_outputs.exc_code == exc_code_ILLEGAL_INSTRUCTION)
            tval = zeroExtend (instr);  // The instruction
         else if (alu_outputs.exc_code == exc_code_INSTR_ADDR_MISALIGNED)
            tval = alu_outputs.addr;    // The branch target pc
         else if (alu_outputs.exc_code == exc_code_BREAKPOINT)
            tval = pc;                  // The faulting virtual address

         let trap_info = Pipe_Trap_Info {epc: pc, exc_code: alu_outputs.exc_code, tval: tval};
         rg_trap_info <= trap_info;
         if (cur_verbosity > 1) begin
            $display ("    CONTROL_TRAP: ", fshow (trap_info));
            $fflush(stdout);
         end

         // If trap is BREAK, and dcsr.ebreakm/s/u is set, enter Debug Mode pause
         // TODO: inline rl_trap_BREAK_to_Debug_Mode here?
`ifdef INCLUDE_GDB_CONTROL
         if (   (alu_outputs.exc_code == exc_code_BREAKPOINT)
`ifdef MIN_CSR
             && (csr_regfile.dcsr_break_enters_debug (m_Priv_Mode))
`else
             && (csr_regfile.dcsr_break_enters_debug (rg_cur_priv))
`endif
            ) begin
             rg_state <= CPU_BREAK;
             if (cur_verbosity > 1) begin
                $display ("    BREAK");
                $fflush(stdout);
             end
         end else rg_state <= CPU_TRAP;
`else
         rg_state <= CPU_TRAP;
`endif
      end

      // ----------------------------------------------------------------

      else begin
         $display ("%06d:[E].%m.rl_run: unrecognized 'control' in alu_outputs", cur_cycle);
         $display ("    ", fshow (alu_outputs));
         $finish (1);
      end
   endrule

   // ================================================================
   // LD completion

   rule rl_LD_completion (
         (rg_state == CPU_LD_COMPLETION)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );
      // Read the saved state ...
      let alu_outputs = rg_alu_outputs;
      let alu_inputs = rg_exec1_inputs;
      let pc = rg_pc;
      let f3 = rg_exec1_inputs.ucontrol.f3;

`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      let word32 <- near_mem.dmem.word32.get ();
      let exc <- near_mem.dmem.exc.get ();

      if (isValid (exc)) begin
         fa_take_trap ("LD: Trap", pc, exc.Valid, alu_outputs.addr);
      end

      else begin
         Bool rd_in_GPR = True;

`ifdef ISA_F
         // Writeback result to FPR
         if (alu_outputs.rd_in_fpr) begin
            WordFL frd_val;
            rd_in_GPR = False;
`ifdef ISA_D
            // Both FLW and FLD are legal instructions
            // A FLW result
            if (f3.is_f3_FLW)
               // needs nan-boxing when destined for a DP register file
               frd_val = fv_nanbox (extend (word32));

            // A FLD result
            // XXX Not functional. The correct thing to do would be to construct
            // the FLD response from two partial responses. 
            else
               frd_val = extend (word32);
`else
            // Only FLW is a legal instruction
            frd_val = word32;
`endif
            // Update the FPR
            fpr_regfile.write_rd (alu_outputs.rd, frd_val);

            // Update MSTATUS.FS -- XXX review
            csr_regfile.ma_update_mstatus_fs (fs_xs_dirty);

            if (cur_verbosity > 1) begin
               $display ("%0d:[D]:%m.rl_LD_completion: FRd [%0d] <= data 0x%08h"
               , cur_cycle, alu_outputs.rd, alu_outputs.frd_val);
               $fflush(stdout);
            end
         end
`endif

         WordXL result = extend (word32);
         if (rd_in_GPR) begin
            gpr_regfile.write_rd (alu_outputs.rd, result);
            if (cur_verbosity > 1) begin
               $display ("%0d:[D]:%m.rl_LD_completion: Rd [%0d] <= data 0x%08h"
                  , cur_cycle, alu_outputs.rd, result);
               $fflush(stdout);
            end
         end

         fa_finish_instr (
              next_pc
            , tagged Valid (tuple2 (alu_outputs.rd, result))
            , tagged Invalid
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );

         // Resume execution
         rg_state <= CPU_RUNNING;
      end
   endrule

   // ================================================================
   // ST completion

   rule rl_ST_completion (
         (rg_state == CPU_ST_COMPLETION)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );
      let word32 <- near_mem.dmem.word32.get ();
      let exc <- near_mem.dmem.exc.get ();
      let alu_inputs = rg_exec1_inputs;

`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      // Read the saved state ...
      let alu_outputs = rg_alu_outputs;
      let pc = rg_pc;

      if (isValid (exc)) 
         fa_take_trap ("ST: Trap", pc, exc.Valid, alu_outputs.addr);

      else begin
         fa_finish_instr (
              next_pc
            , tagged Invalid
            , tagged Valid (tuple2 (alu_outputs.addr, alu_outputs.val2))
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );

         // Resume execution
         rg_state <= CPU_RUNNING;

         if (cur_verbosity > 1) begin
            $display ("%0d:[D]:%m.rl_ST_completion", cur_cycle);
            $fflush(stdout);
         end
      end
   endrule

   // ================================================================
   // These pragamas are required to let the scheduler know that the DMem and IMem
   // won't be accessed simultaneously.
   
`ifdef ISA_C
   (* mutually_exclusive = "imem_c_rl_NEW_RSP, rl_exec1" *)
   (* mutually_exclusive = "imem_c_rl_new_req, rl_exec1" *)
`endif


   // ================================================================
   // AMO completion

`ifdef ISA_A
   rule rl_AMO_completion (rg_state == CPU_AMO_COMPLETION);
      // Read the saved state ...
      let alu_outputs = rg_alu_outputs;
      let pc = rg_pc;
      let word32 <- near_mem.dmem.word32.get ();
      let exc <- near_mem.dmem.exc.get ();
      let alu_inputs  = rg_exec1_inputs;
`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      if (isValid (exc)) begin
         fa_take_trap ("AMO: Trap", pc, exc.Valid, alu_outputs.addr);
      end

      else begin
         // Writeback result
         WordXL result = extend (word32);
         gpr_regfile.write_rd (alu_outputs.rd, result);

         fa_finish_instr (
              next_pc
            , tagged Valid (tuple2 (alu_outputs.rd, result))
            , tagged Invalid
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );

         // Resume execution
         rg_state <= CPU_RUNNING;

         if (cur_verbosity > 1) begin
            $display ("%0d:[D]:%m.rl_AMO_completion: Rd [%0d] <= data 0x%08h", cur_cycle, alu_outputs.rd, result);
            $fflush(stdout);
         end
      end
   endrule
`endif

   // ================================================================
   // M completion (int MUL/DIV/REM)

`ifdef ISA_M
   rule rl_M_completion (
         (rg_state == CPU_M_COMPLETION)
      && (mbox.valid)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );
      // Read the saved state ...
      let alu_outputs = rg_alu_outputs;
      let alu_inputs  = rg_exec1_inputs;
`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      // Writeback result
      let result = mbox.word;
      gpr_regfile.write_rd (alu_outputs.rd, result);

      fa_finish_instr (
           next_pc
         , tagged Valid (tuple2 (alu_outputs.rd, result))
         , tagged Invalid
`ifndef MIN_CSR
         , rg_cur_priv
`endif
      );

      // Resume execution
      rg_state <= CPU_RUNNING;

      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_M_completion: Rd [%0d] <= data 0x%08h", cur_cycle, alu_outputs.rd, result);
         $fflush(stdout);
      end
   endrule
`endif

   // ================================================================
   // FD completion (floating point)
   // TODO: Needs fixup; should write back to FPR or GPR depending on instr, etc.

`ifdef ISA_F
   rule rl_FD_completion ((rg_state == CPU_FD_COMPLETION) && (fbox.valid));

      // Read the saved state ...
      let alu_outputs = rg_alu_outputs;
      let alu_inputs  = rg_exec1_inputs;
`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      // Extract fields from FBOX result
      match { .value, .fflags } = fbox.word;

`ifdef ISA_D
      let frd_val = value;
`else
      let frd_val = truncate (value);
`endif

      if (alu_outputs.rd_in_fpr)
         fpr_regfile.write_rd (alu_outputs.rd, frd_val);
      else
         gpr_regfile.write_rd (alu_outputs.rd, truncate (value));

      // Update FCSR.fflags
      csr_regfile.ma_update_fcsr_fflags (fflags);

      // Update MSTATUS.FS
      if (alu_outputs.rd_in_fpr)
         csr_regfile.ma_update_mstatus_fs (fs_xs_dirty);

      // XXX Does not actually record register updates
      fa_finish_instr (
           next_pc
         , tagged Invalid
         , tagged Invalid
`ifndef MIN_CSR
         , rg_cur_priv
`endif
      );

      // Resume execution
      rg_state <= CPU_RUNNING;

      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_FD_completion: Rd [%0d] <= data 0x%08h", cur_cycle, alu_outputs.rd, value);
         $fflush(stdout)
      end
   endrule
`endif

   // ================================================================
   // SH completion

`ifdef SHIFT_SERIAL
   rule rl_SH_completion (
         (rg_state == CPU_SH_COMPLETION)
      && (sbox.valid)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );
      // Read the saved state ...
      let alu_outputs = rg_alu_outputs;
      let alu_inputs  = rg_exec1_inputs;
`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      // Writeback result
      let result = sbox.word;
      gpr_regfile.write_rd (alu_outputs.rd, result);

      fa_finish_instr (
           next_pc
         , tagged Valid (tuple2 (alu_outputs.rd, result))
         , tagged Invalid
`ifndef MIN_CSR
         , rg_cur_priv
`endif
      );

      // Resume execution
      rg_state <= CPU_RUNNING;

      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_SH_completion: Rd [%0d] <= data 0x%08h"
            , cur_cycle, alu_outputs.rd, result);
         $fflush(stdout);
      end
   endrule
`endif


   // ================================================================
   // CSRR_W completion

   rule rl_CSRR_W_completion (
         (rg_state == CPU_CSRR_W_COMPLETION)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );
      // Read the saved state ...
      let alu_outputs= rg_alu_outputs;
      let instr      = rg_exec1_inputs.instr;
      let pc         = rg_pc;
      let alu_inputs = rg_exec1_inputs;
`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      let csr_addr   = instr_csr (instr);
      let rs1        = instr_rs1 (instr);   // only debug
      let rs1_val    = alu_outputs.val1;
      let rd         = alu_outputs.rd;

      if (! rg_csr_permitted) begin
         fa_take_trap ("CSRR_W: Trap on CSR permissions"
            , pc, exc_code_ILLEGAL_INSTRUCTION, zeroExtend (instr));
      end
      else begin
         // Read the CSR only if Rd is not 0
         WordXL csr_val = ?;
         if (rd != 0) begin
            // TODO: csr_regfile.read should become ActionValue (it may have side effects)
            let m_csr_val = csr_regfile.read_csr (csr_addr);
            csr_val   = fromMaybe (?, m_csr_val);
         end

         // Writeback to GPR file
         let new_rd_val = csr_val;
         gpr_regfile.write_rd (rd, new_rd_val);

         // Writeback to CSR file
         let new_csr_val <- csr_regfile.mav_csr_write (csr_addr, rs1_val);

         // Finish the instruction
         fa_finish_instr (
              next_pc
            , tagged Valid (tuple2 (rd, new_rd_val))
            , tagged Invalid
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );

         // Resume execution
         rg_state <= CPU_RUNNING;

         // Debug
         if (cur_verbosity > 1) begin
            $display ("%0d:[D]:%m.rl_CSRR_W_COMPLETION: Rs1 %0d Rs1_val 0x%0h csr 0x%0h csr_val 0x%0h Rd %0d",
                      cur_cycle, rs1, rs1_val, csr_addr, csr_val, rd);
            $fflush(stdout);
         end
      end
   endrule

   // ================================================================
   // CSRR_S, CSRR_C completion

   rule rl_CSRR_S_or_C_completion (
         (rg_state == CPU_CSRR_S_C_COMPLETION)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );
      // Read the saved state ...
      let alu_outputs   = rg_alu_outputs;
      let alu_inputs    = rg_exec1_inputs;
      let instr         = alu_inputs.instr;
      let f3            = alu_inputs.ucontrol.f3;
      let pc            = rg_pc;
`ifdef ISA_C
      let next_pc = pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = pc + 4;
`endif

      let rs1_val       = alu_outputs.val1;
      let rd            = alu_outputs.rd;

      let csr_addr      = instr_csr (instr);
      let rs1           = instr_rs1 (instr);   // only debug

      if (! rg_csr_permitted) begin
         fa_take_trap ( "CSRR_S_or_C: Trap on CSR permissions"
            , pc, exc_code_ILLEGAL_INSTRUCTION, zeroExtend (instr));
      end
      else begin
         // Read the CSR
         // TODO: csr_regfile.read should become ActionValue (it may have side effects)
         let m_csr_val  = csr_regfile.read_csr (csr_addr);
         WordXL csr_val = fromMaybe (?, m_csr_val);

         // Writeback to GPR file
         let new_rd_val = csr_val;
         gpr_regfile.write_rd (rd, new_rd_val);

         // Writeback to CSR file, but only if rs1 != 0
         let x = (  ((f3.is_f3_CSRRS) || (f3.is_f3_CSRRSI))
                  ? (csr_val | rs1_val)                // CSRRS, CSRRSI
                  : csr_val & (~ rs1_val));            // CSRRC, CSRRCI

         let csr_wr_result = CSR_Write_Result {new_csr_value:    0,
                                               m_new_csr_value2: tagged Invalid};
         if (rs1 != 0) begin
            csr_wr_result <- csr_regfile.mav_csr_write (csr_addr, x);
         end

         // Finish the instruction
         fa_finish_instr (
              next_pc
            , tagged Valid (tuple2 (rd, new_rd_val))
            , tagged Invalid
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );

         // Resume execution
         rg_state <= CPU_RUNNING;

         // Debug
         if (cur_verbosity > 1) begin
            $display ("%0d:[D]:%m.rl_CSRR_S_or_C_COMPLETION: Rs1 %0d Rs1_val 0x%0h csr 0x%0h csr_val 0x%0h Rd %0d",
                      cur_cycle, rs1, rs1_val, csr_addr, csr_val, rd);
            $display ("    New csr_val(s): ", fshow (csr_wr_result));
            $fflush(stdout);
         end
      end
   endrule


   // ================================================================
   // Traps (except BREAKs that enter Debug Mode)

   rule rl_trap (
         (rg_state == CPU_TRAP)
`ifdef EVAL
      && (!cyc_exp)
`endif
`ifdef INCLUDE_GDB_CONTROL
      && (! rg_halt)
`endif
   );
      let epc      = rg_trap_info.epc;
      let exc_code = rg_trap_info.exc_code;
      let tval     = rg_trap_info.tval;
      let instr    = rg_exec1_inputs.instr;

      // Take trap
      let csr_trap_info <- csr_regfile.csr_trap_actions (
`ifndef MIN_CSR
         rg_cur_priv,   // from privilege
`endif
         epc,
`ifndef MIN_CSR
         False,         // NMI
`endif
         False,         // interrupt_req
         exc_code
         , tval
      );
`ifdef MIN_CSR
      let next_pc    = csr_trap_info;
`else
      let next_pc    = csr_trap_info.pc;
      let new_mstatus= csr_trap_info.mstatus;
      let mcause     = csr_trap_info.mcause;

      rg_cur_priv <= csr_trap_info.priv;
`endif

      // Reusing the alu_inputs structure because it is unused during an interrupt/trap. 
      rg_pc <= next_pc;

      rg_state <= CPU_RESTART_TRAP;

`ifndef SYNTHESIS
      // Simulation heuristic: finish if trap back to this instr
      if (epc == next_pc) begin
         $display ("%06d:[D]:%m.rl_trap: Tight infinite trap loop: pc 0x%0x instr 0x%08x",
                   cur_cycle, next_pc, instr);
`ifndef TCM_LOADER
         // We do not finish the simulation when simulating with a TCM loader
         // because a base loader might place an infinite trap loop waiting for
         // GDB to connect.
         fa_report_CPI;
         $finish (0);
`endif
      end
`endif

      // Debug
      if (cur_verbosity != 0) begin
`ifdef MIN_CSR
	 $display ("%0d:[D]:%m.rl_trap: epc 0x%0h  instr 0x%08h  exc_code %0d  tval 0x%0d ",
		   cur_cycle, epc, instr, exc_code, tval);
         $display ("    new_pc (=mtvec) 0x%0h", next_pc);
`else
	 $display ("%0d:[D]:%m.rl_trap: epc 0x%0h  instr 0x%08h  exc_code %0d  tval 0x%0d  mcause ",
		   cur_cycle, epc, instr, exc_code, tval, fshow (mcause));
	 $display ("    new_priv %0d  new_pc (=mtvec) 0x%0h  new mstatus 0x%0h",
		   csr_trap_info.priv, next_pc, new_mstatus);
`endif
         $fflush(stdout);
      end
   endrule

   rule rl_restart_trap (
      (rg_state == CPU_RESTART_TRAP)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );

`ifdef MIN_CSR
      fa_start_ifetch (rg_pc);
`else
      fa_start_ifetch (rg_pc, rg_cur_priv);
`endif
      rg_state <= CPU_RUNNING;
      if (cur_verbosity > 1)
         $display ("%0d:[D]:%m.rl_restart_trap: pc 0x%0h", cur_cycle, rg_pc);
   endrule

   // ================================================================
   // Debug Mode (enter on BREAK trap when dcsr.ebreakm/s/u is set)

`ifdef INCLUDE_GDB_CONTROL
   rule rl_trap_BREAK_to_Debug_Mode ((rg_state == CPU_BREAK) && (! rg_halt));
      let pc = rg_pc;
      let instr = rg_exec1_inputs.instr;
      if (cur_verbosity > 0) begin
         $display ("%0d: CPU.rl_trap_BREAK_to_Debug_Mode: PC 0x%08h instr 0x%08h"
            , cur_cycle, pc, instr);
         $fflush(stdout);
      end

`ifdef MIN_CSR
      csr_regfile.write_dcsr_cause_priv (DCSR_CAUSE_EBREAK, m_Priv_Mode);
`else
      csr_regfile.write_dcsr_cause_priv (DCSR_CAUSE_EBREAK, rg_cur_priv);
`endif
      csr_regfile.write_dpc (pc);    // Where we'll resume on 'continue'
      rg_state <= CPU_DEBUG_MODE;
`ifndef SYNTHESIS
      fa_report_CPI;
`endif

      // Notify debugger that we've halted
      f_run_halt_rsps.enq (False);
   endrule
`endif

   // ----------------
   // Reset while in Debug Mode (GDB or TCM Loader)

   rule rl_reset_from_Debug_Mode (   (rg_state == CPU_DEBUG_MODE)
                                  && f_reset_reqs.notEmpty);
      rg_state <= CPU_RESET1;
   endrule

   // Reset while in RUNNING mode (TCM Loader path)
   rule rl_reset_from_RUNNING (   (rg_state == CPU_RUNNING)
                               && (f_reset_reqs.notEmpty));
      rg_state <= CPU_RESET1;
   endrule

   // ================================================================
   // SFENCE.VMA

`ifdef ISA_PRIV_S
   rule rl_SFENCE_VMA_COMPLETION (rg_state == CPU_SFENCE_VMA_COMPLETION);
      if (cur_verbosity > 1) begin
         $display ("%d:[D]:%m.rl_SFENCE_VMA_COMPLETION", cur_cycle);
         $fflush(stdout);
      end

      let alu_inputs  = rg_exec1_inputs;
`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      // Await SFENCE.VMA completion
      let dummy <- near_mem.sfence_vma_server.response.get;

      // Resume pipe
      rg_state <= CPU_RUNNING;
         fa_finish_instr (
              next_pc
            , tagged Invalid
            , tagged Invalid
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );
   endrule
`endif

   // ================================================================
   // WFI_PAUSED state

   rule rl_WFI_resume (
         (rg_state == CPU_WFI_PAUSED)
      && (! f_reset_reqs.notEmpty)
      && (csr_regfile.wfi_resume)
`ifdef EVAL
      && (!cyc_exp)
`endif
   );

      let pc         = rg_pc;
      let alu_inputs = rg_exec1_inputs;
      let instr      = alu_inputs.instr;
`ifdef ISA_C
      let next_pc = rg_pc + (alu_inputs.is_i32_not_i16 ? 4 : 2);
`else
      let next_pc = rg_pc + 4;
`endif

      // Debug
      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_WFI_resume", cur_cycle);
         $fflush(stdout);
      end

      // Resume pipe (it will handle the interrupt, if one is pending)
      rg_state <= CPU_RUNNING;
         fa_finish_instr (
              next_pc
            , tagged Invalid
            , tagged Invalid
`ifndef MIN_CSR
            , rg_cur_priv
`endif
         );
   endrule: rl_WFI_resume

   // ----------------
   // Allow resets to always happen when cyc_exp has happened
   rule rl_reset_from_WFI (
         (rg_state == CPU_WFI_PAUSED)
      && f_reset_reqs.notEmpty
   );
      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_reset_from_WFI", cur_cycle);
         $fflush(stdout);
      end

      rg_state <= CPU_RESET1;
   endrule: rl_reset_from_WFI

   // ================================================================
   // EXTERNAL and GDB INTERRUPTS while running
`ifdef MIN_CSR
   rule rl_take_external_interrupt (    csr_regfile.interrupt_pending ()
`else
   rule rl_take_external_interrupt (    csr_regfile.interrupt_pending (rg_cur_priv)
`endif
                                        matches tagged Valid .exc_code
                                    &&& (rg_state == CPU_INTERRUPT_PENDING));

      // Remember the PC on whose fetch the interrupt occured
      let epc     = rg_pc;

      // Take trap
      let csr_trap_info <- csr_regfile.csr_trap_actions (
`ifndef MIN_CSR
         rg_cur_priv,   // from priv
`endif
         epc,
`ifndef MIN_CSR
         False,         // NMI
`endif
         True,          // interrupt_req
         exc_code
         , 0            // tval
      );
                                                     

      // Save the PC and the PRIV to restart operations
`ifdef MIN_CSR
      rg_pc         <= csr_trap_info;
`else
      rg_cur_priv   <= csr_trap_info.priv;
      rg_pc         <= csr_trap_info.pc;
`endif
      rg_state <= CPU_RESTART_EXT_INT;

      // Debug
      if (cur_verbosity > 0) begin
`ifdef MIN_CSR
         $display ("%0d:[D]:%m.rl_take_external_interrupt; epc 0x%0h, pc 0x%0h",
                   cur_cycle, epc, csr_trap_info);
`else
	 $display ("%0d:[D]:%m.rl_take_external_interrupt; epc 0x%0h, pc 0x%0h, new mstatus 0x%0h",
		   cur_cycle, epc, csr_trap_info.pc, csr_trap_info.mstatus);
`endif
         $fflush(stdout);
      end
   endrule

   rule rl_restart_external_interrupt (rg_state == CPU_RESTART_EXT_INT);
`ifdef ISA_PRIV_S
      Bit #(1) sstatus_SUM = mstatus [18];    // TODO: project new_mstatus to new_sstatus?
      Bit #(1) mstatus_MXR = mstatus [19];
`endif

      // Directly invoke the imem request
      imem.req (rg_pc);
      rg_state <= CPU_RUNNING;
      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_restart_external_interrupt: pc 0x%0h", cur_cycle, rg_pc);
         $fflush(stdout);
      end
   endrule

   // ----------------
   // Handle debugger stop-request and dcsr.step step-request while running
   // and no interrupt pending

`ifdef INCLUDE_GDB_CONTROL
   rule rl_stop (   (rg_state == CPU_RUNNING)
                 && rg_halt
                 && (! interrupt_pending)
                 && (rg_stop_req || rg_step_req));

      let pc = rg_pc;
      let instr = rg_exec1_inputs.instr;

      // Report CPI only stop-req, but not on step-req (where it's not very useful)
      if (rg_stop_req) begin
         $display ("%0d:[D]:%m.rl_stop: Stop for debugger. PC = 0x%08h", cur_cycle, pc);
         $fflush(stdout);
`ifndef SYNTHESIS
         fa_report_CPI;
`endif
      end
      else begin
         $display ("%0d:[D]:%m.rl_stop: Stop after single-step. PC = 0x%08h", cur_cycle, pc);
         $fflush(stdout);
      end

      DCSR_Cause cause= (rg_stop_req ? DCSR_CAUSE_HALTREQ : DCSR_CAUSE_STEP);
`ifdef MIN_CSR
      csr_regfile.write_dcsr_cause_priv (cause, m_Priv_Mode);
`else
      csr_regfile.write_dcsr_cause_priv (cause, rg_cur_priv);
`endif
      csr_regfile.write_dpc (pc);    // We'll retry this instruction on 'continue'
      rg_state    <= CPU_DEBUG_MODE;
      rg_halt     <= False;

      rg_stop_req <= False;
      rg_step_req <= False;

      // Notify debugger that we've halted
      f_run_halt_rsps.enq (False);

      // Accounting: none (instruction was abandoned)

      // Debug
      if (cur_verbosity > 0) begin
         $display ("%0d:[D]:%m.rl_stop: (next) PC: 0x%0h", cur_cycle, pc);
         $fflush(stdout);
      end
   endrule
`endif

   // ================================================================
   // ================================================================
   // ================================================================
   // DEBUGGER ACCESS

   // ----------------
   // Debug Module Run/Halt control

`ifdef INCLUDE_GDB_CONTROL
   rule rl_debug_run (   (f_run_halt_reqs.first == True)
                      && (rg_state == CPU_DEBUG_MODE));
      f_run_halt_reqs.deq;

      // Debugger 'resume' request (e.g., GDB 'continue' command)
      let dpc = csr_regfile.read_dpc;
      fa_restart (dpc);
      if (cur_verbosity > 1) begin
         $display ("%0d: CPU.rl_debug_run: 'run' from dpc 0x%0h", cur_cycle, dpc);
         $fflush(stdout);
      end
   endrule

   rule rl_debug_run_ignore (   (f_run_halt_reqs.first == True)
                             && (fn_is_running (rg_state)));
      f_run_halt_reqs.deq;

      // Notify debugger that we are running
      f_run_halt_rsps.enq (True);

      $display ("%0d: CPU.debug_run_ignore: ignoring 'run' command (CPU is not in Debug Mode)", cur_cycle);
      $fflush(stdout);
   endrule

   rule rl_debug_halt (   (f_run_halt_reqs.first == False)
                       && (fn_is_running (rg_state)));
      f_run_halt_reqs.deq;

      // Debugger 'halt' request (e.g., GDB '^C' command)
      rg_stop_req <= True;
      if (cur_verbosity > 1) begin
         $display ("%0d: CPU.rl_debug_halt", cur_cycle);
         $fflush(stdout);
      end
   endrule

   rule rl_debug_halt_ignore (   (f_run_halt_reqs.first == False)
                              && (! fn_is_running (rg_state)));
      f_run_halt_reqs.deq;

      // Notify debugger that we've halted
      f_run_halt_rsps.enq (False);

      $display ("%0d: CPU.rl_debug_halt_ignore: ignoring 'halt' (CPU already halted)", cur_cycle);
   endrule

   // ----------------
   // Debug Module GPR read/write

   rule rl_debug_read_gpr (   (rg_state == CPU_DEBUG_MODE)
                           && (! f_gpr_reqs.first.write));
      let req <- pop (f_gpr_reqs);
      Bit #(5) regname = req.address;
      let data = gpr_regfile.read_rs1 (regname);
      let rsp = DM_CPU_Rsp {ok: True, data: data};
      f_gpr_rsps.enq (rsp);
      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_debug_read_gpr: reg %0d => 0x%0h",
                   cur_cycle, regname, data);
         $fflush(stdout);
      end
   endrule

   rule rl_debug_write_gpr (   (rg_state == CPU_DEBUG_MODE)
                            && (f_gpr_reqs.first.write));
      let req <- pop (f_gpr_reqs);
      Bit #(5) regname = req.address;
      let data = req.data;
      gpr_regfile.write_rd (regname, data);

      let rsp = DM_CPU_Rsp {ok: True, data: ?};
      f_gpr_rsps.enq (rsp);

      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_debug_write_gpr: reg %0d <= 0x%0h",
                   cur_cycle, regname, data);
         $fflush(stdout);
      end
   endrule

`ifdef ISA_F
   // ----------------
   // Debug Module FPR read/write

   rule rl_debug_read_fpr (   (rg_state == CPU_DEBUG_MODE)
                           && (! f_fpr_reqs.first.write));
      let req <- pop (f_fpr_reqs);
      Bit #(5) regname = req.address;
      let data = fpr_regfile.read_rs1 (regname);
      let rsp = DM_CPU_Rsp {ok: True, data: data};
      f_fpr_rsps.enq (rsp);
      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_debug_read_fpr: reg %0d => 0x%0h",
                   cur_cycle, regname, data);
         $fflush(stdout);
      end
   endrule

   rule rl_debug_write_fpr (   (rg_state == CPU_DEBUG_MODE)
                            && (f_fpr_reqs.first.write));
      let req <- pop (f_fpr_reqs);
      Bit #(5) regname = req.address;
      let data = req.data;
      fpr_regfile.write_rd (regname, data);

      let rsp = DM_CPU_Rsp {ok: True, data: ?};
      f_fpr_rsps.enq (rsp);

      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_debug_write_fpr: reg %0d <= 0x%0h",
                   cur_cycle, regname, data);
         $fflush(stdout);
      end
   endrule
`endif
   // ----------------
   // Debug Module CSR read/write

   rule rl_debug_read_csr (   (rg_state == CPU_DEBUG_MODE)
                           && (!f_csr_reqs.first.write));
      let req <- pop (f_csr_reqs);
      Bit #(12) csr_addr = req.address;
      let m_data = csr_regfile.read_csr (csr_addr);
      let data = fromMaybe (?, m_data);
      let rsp = DM_CPU_Rsp {ok: True, data: data};
      f_csr_rsps.enq (rsp);
      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_debug_read_csr: csr %0d => 0x%0h",
                   cur_cycle, csr_addr, data);
         $fflush(stdout);
      end
   endrule

   rule rl_debug_write_csr (   (rg_state == CPU_DEBUG_MODE)
                            && (f_csr_reqs.first.write));
      let req <- pop (f_csr_reqs);
      Bit #(12) csr_addr = req.address;
      let data = req.data;
      let new_csr_val <- csr_regfile.mav_csr_write (csr_addr, data);

      let rsp = DM_CPU_Rsp {ok: True, data: ?};
      f_csr_rsps.enq (rsp);

      if (cur_verbosity > 1) begin
         $display ("%0d:[D]:%m.rl_debug_write_csr: csr 0x%0h 0x%0h <= 0x%0h",
                   cur_cycle, csr_addr, data, new_csr_val);
         $fflush(stdout);
      end
   endrule
`endif

   // ================================================================
   // ================================================================
   // ================================================================
   // INTERFACE


   // ----------------
   // SoC fabric connections

`ifdef Near_Mem_TCM
   // Fabric side (MMIO initiator interface)
   interface dmem_master = near_mem.dmem_master;
`else
   // IMem to fabric master interface
   interface imem_master = near_mem.imem_master;

   // DMem to fabric master interface
   interface mem_master = near_mem.mem_master;
`endif

   // ----------------
   // Interface to 'coherent DMA' port of optional L2 cache
   // (non-coherent DMA backdoor for TCMs)

`ifdef INCLUDE_GDB_CONTROL
   interface Server dbg_server = near_mem.dbg_server;
`endif

`ifdef Near_Mem_TCM
`ifdef TCM_LOADER
   interface Server dma_server = near_mem.dma_server;
`endif
`endif

   // ----------------------------------------------------------------
   // External interrupts

   method Action  m_external_interrupt_req (x) = csr_regfile.m_external_interrupt_req (x);
`ifndef MIN_CSR
   method Action  s_external_interrupt_req (x) = csr_regfile.s_external_interrupt_req (x);
`endif

   // ----------------
   // Software and timer interrupts (from Near_Mem_IO/CLINT)

   method Action  software_interrupt_req (x) = csr_regfile.software_interrupt_req (x);
   method Action  timer_interrupt_req    (x) = csr_regfile.timer_interrupt_req    (x);

`ifndef MIN_CSR
   // ----------------
   // Non-maskable interrupt

   method Action  nmi_req (x);
      csr_regfile.nmi_req (x);
   endmethod
`endif

   // ----------------
   // Optional interface to Tandem Verifier

`ifdef INCLUDE_TANDEM_VERIF
   interface Get  trace_data_out = toGet (f_trace_data);
`endif

   // ----------------
   // Optional interface to Debug Module

`ifdef INCLUDE_GDB_CONTROL
   interface CPU_DM_Ifc debug;
      // Reset
      interface Server  hart_reset_server = toGPServer (f_reset_reqs, f_reset_rsps);

      // run-control, other
      interface Server  hart_server_run_halt = toGPServer (f_run_halt_reqs, f_run_halt_rsps);

      interface Put  hart_put_other_req;
         method Action put (Bit #(4) req);
`ifdef SYNTHESIS
            noAction;
`else
            cfg_verbosity <= truncate (req);
`endif
         endmethod
      endinterface

      // GPR access
      interface Server  hart_gpr_mem_server = toGPServer (f_gpr_reqs, f_gpr_rsps);

`ifdef ISA_F
      // FPR access
      interface Server  hart_fpr_mem_server = toGPServer (f_fpr_reqs, f_fpr_rsps);
`endif

      // CSR access
      interface Server  hart_csr_mem_server = toGPServer (f_csr_reqs, f_csr_rsps);
   endinterface
`else
   // Reset
   interface Server  hart_reset_server = toGPServer (f_reset_reqs, f_reset_rsps);
`endif

   // ----------------------------------------------------------------
   // Misc. control and status

`ifndef SYNTHESIS
   // ----------------
   // For tracing
   method Action  set_verbosity (Bit #(2)  verbosity);
      cfg_verbosity <= verbosity;
   endmethod
`endif

   // ----------------
   // For ISA tests: watch memory writes to <tohost> addr

`ifdef Near_Mem_TCM
`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Fabric_Addr tohost_addr);
      near_mem.set_watch_tohost (watch_tohost, tohost_addr);
   endmethod

   method Fabric_Data mv_tohost_value = near_mem.mv_tohost_value;
`endif
`endif

endmodule: mkCPU

// ================================================================

endpackage
