// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

package CSR_RegFile_Min;

// ================================================================
// CSR (Control and Status Register) Register File

// Supports a minimal set of machine mode CSRs.

// ================================================================
// Exports

export  CSR_Write_Result (..);
export  CSR_RegFile_IFC (..);
export  mkCSR_RegFile;

// ================================================================
// BSV library imports

import ConfigReg    :: *;
import RegFile      :: *;
import Vector       :: *;
import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;

// BSV additional libs

import GetPut_Aux :: *;

// ================================================================
// Project imports

import Cur_Cycle    :: *;
import ISA_Decls :: *;
import Core_Map  :: *;

`ifdef INCLUDE_GDB_CONTROL
import DM_Common :: *;    // Debug Module defs
`endif

import CSR_MSTATUS_Min :: *;
import CSR_MIP_Min     :: *;
import CSR_MIE_Min     :: *;

// ================================================================
// Writing a CSR can update multiple CSRs (e.g., writing
// FRM/FFLAGS/FCSR also updates MSTATUS.FS and MSTATUS.SD

typedef struct {
   WordXL           new_csr_value;
   Maybe #(WordXL)  m_new_csr_value2;
   }
CSR_Write_Result
deriving (Bits, FShow);

// ================================================================
// INTERFACE

interface CSR_RegFile_IFC;
   // Reset
   interface Server #(Token, Token) server_reset;

   // CSR read (w.o. side effect)
   (* always_ready *)
   method Maybe #(Word) read_csr (CSR_Addr csr_addr);

   // CSR write (returning new value)
   (* always_ready *)
   method ActionValue #(CSR_Write_Result) mav_csr_write (CSR_Addr csr_addr, WordXL word);

   // Read MSTATUS
   (* always_ready *)
   method WordXL read_mstatus;

   // CSR trap actions
   method ActionValue #(Addr)
          csr_trap_actions (Word       pc,
                            Bool       interrupt,  // other interrupt
                            Exc_Code   exc_code,
                            Word       xtval);

   // CSR RET actions (return from exception)
   method ActionValue #(Addr) csr_ret_actions ();

   // Read MINSTRET
   (* always_ready *)
   method Bit #(64) read_csr_minstret;

   // Increment MINSTRET
   (* always_ready *)
   method Action csr_minstret_incr;

   // Read MCYCLE
   (* always_ready *)
   method Bit #(64) read_csr_mcycle;

   // Read MISA
   (* always_ready *)
   method MISA read_misa;

   // Read MTIME
   (* always_ready *)
   method Bit #(64) read_csr_mtime;

   // Access permission
   (* always_ready *)
   method Bool access_permitted (CSR_Addr csr_addr, Bool read_not_write);

   // Read MIP
   (* always_ready *)
   method WordXL csr_mip_read;

   // ----------------
   // Interrupts

   (* always_ready, always_enabled *)
   method Action m_external_interrupt_req (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action timer_interrupt_req    (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action software_interrupt_req (Bool set_not_clear);

   (* always_ready *)
   method Maybe #(Exc_Code) interrupt_pending;

   // WFI ignores mstatus ies and ideleg regs
   (* always_ready *)
   method Bool wfi_resume;

   // ----------------
   // Methods when Debug Module is present

`ifdef INCLUDE_GDB_CONTROL
   // Read dpc
   method Word read_dpc ();

   // Update dpc
   method Action write_dpc (Addr pc);

   // Break should enter Debug Mode
   method Bool dcsr_break_enters_debug (Priv_Mode cur_priv);

   // Read dcsr.step
   method Bool read_dcsr_step ();

   // Update 'cause' and 'priv' in DCSR
   (* always_ready *)
   method Action write_dcsr_cause_priv (DCSR_Cause  cause, Priv_Mode  priv);

`endif

   // ----------------
   // Debugging this module

   method Action debug;
endinterface

// ================================================================
// 'misa' specifying RSIC-V features implemented.

function MISA misa_reset_value;
   MISA ms = unpack (0);

`ifdef RV32
   ms.mxl = misa_mxl_32;
`elsif RV64
   ms.mxl = misa_mxl_64;
`elsif RV128
   ms.mxl = misa_mxl_128;
`else
   ms.mxl = misa_mxl_zero;
`endif

`ifdef ISA_PRIV_U
   // User Mode
   ms.u = 1'b1;
`ifdef ISA_N
   // User-level Interrupts
   ms.n = 1'b1;
`endif
`endif

`ifdef ISA_PRIV_S
   // Supervisor Mode
   ms.s = 1'b1;
`endif

   // Integer Base
   ms.i = 1'b1;

`ifdef ISA_M
   // Integer Multiply/Divide
   ms.m = 1'b1;
`endif

`ifdef ISA_F
   // Single- and Double-precision Floating Point
   ms.f = 1'b1;
`endif

`ifdef ISA_D
   ms.d = 1'b1;
`endif

`ifdef ISA_A
   // Atomic Memory Ops
   ms.a = 1'b1;
`endif

`ifdef ISA_C
   // Compressed Instructions
   ms.c = 1'b1;
`endif

   return ms;
endfunction

// ================================================================
// Major states of mkCSR_RegFile module

typedef enum { RF_RESET_START, RF_RUNNING } RF_State
deriving (Eq, Bits, FShow);

// ================================================================

(* synthesize *)
module mkCSR_RegFile (CSR_RegFile_IFC);

   Bit #(2) verbosity = 0;
   Reg #(RF_State) rg_state      <- mkReg (RF_RESET_START);
   MISA              misa          =  misa_reset_value;

   Core_Map_IFC addr_map <- mkCore_Map;

   // Reset
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   // Supervisor-mode CSRs
   Bit #(16)  sedeleg = 0;    // hardwired to 0
   Bit #(12)  sideleg = 0;    // hardwired to 0

   Bit #(16)         rg_medeleg   = 0;
   Bit #(12)         rg_mideleg   = 0;

   // Machine-mode CSRs
   Word mvendorid   = 0;    // Not implemented
   Word marchid     = 0;    // Not implemented
   Word mimpid      = 0;    // Not implemented
   Word mhartid     = 0;

   CSR_MSTATUS_IFC  csr_mstatus <- mkCSR_MSTATUS;

   CSR_MIE_IFC       csr_mie       <- mkCSR_MIE;
   CSR_MIP_IFC       csr_mip       <- mkCSR_MIP;

   Reg #(MTVec)      rg_mtvec      <- mkRegU;

   Reg #(Word)       rg_mscratch <- mkRegU;
   Reg #(Word)       rg_mepc     <- mkRegU;
   Reg #(MCause)     rg_mcause   <- mkRegU;
   Reg #(Word)       rg_mtval    <- mkRegU;

   // mcycle is needed even for user-mode RDCYCLE instruction
   // It can be updated by a CSR instruction (in Priv_M), and by the clock
   Reg #(Bit #(64))   rg_mcycle <- mkReg (0);
   RWire #(Bit #(64)) rw_mcycle <- mkRWire;    // Driven on CSRRx write to mcycle

   // minstret is needed even for user-mode RDINSTRET instructions
   // It can be updated by a CSR instruction (in Priv_M), and by retirement of any other instruction
   Reg #(Bit #(64))   rg_minstret      <- mkReg (0);    // Needed even for user-mode instrs
   RWire #(Bit #(64)) rw_minstret      <- mkRWire;      // Driven on CSRRx write to minstret
   PulseWire          pw_minstret_incr <- mkPulseWire;

`ifdef INCLUDE_GDB_CONTROL
   // Debug
   Reg #(Bit #(32)) rg_dcsr      <- mkRegU;    // Is 32b even in RV64
   Reg #(WordXL)    rg_dpc       <- mkRegU;
   Reg #(WordXL)    rg_dscratch0 <- mkRegU;
   Reg #(WordXL)    rg_dscratch1 <- mkRegU;
`endif

   // ================================================================
   // BEHAVIOR: RESET
   // Initialize some CSRs.

   rule rl_reset_start (rg_state == RF_RESET_START);
      // Machine-level CSRs
      csr_mstatus.reset;
      csr_mie.reset;
      csr_mip.reset;

      rg_mtvec      <= word_to_mtvec (truncate (addr_map.m_mtvec_reset_value));
      rg_mcause     <= word_to_mcause (0);    // Supposed to be the cause of the reset.
      rw_minstret.wset (0);

`ifdef INCLUDE_GDB_CONTROL
      rg_dpc  <= truncate (addr_map.m_pc_reset_value);
      rg_dcsr <= zeroExtend ({4'h4,    // [31:28]  xdebugver
                              12'h0,   // [27:16]  reserved
                              1'h0,    // [15]     ebreakm
                              1'h0,    // [14]     reserved
                              1'h0,    // [13]     ebreaks
                              1'h0,    // [12]     ebreaku
                              1'h0,    // [11]     stepie
                              1'h0,    // [10]     stopcount
                              1'h0,    // [9]      stoptime
                              3'h0,    // [8:7]    cause    // WARNING: 0 is non-standard
                              1'h0,    // [5]      reserved
                              1'h1,    // [4]      mprven
                              1'h0,    // [3]      nmip    // non-maskable interrupt pending
                              1'h0,    // [2]      step
                              m_Priv_Mode}    // [1:0]    prv (machine mode)
                             );
`endif

      rg_state <= RF_RUNNING;
   endrule

   // ================================================================
   // BEHAVIOR

   // ----------------------------------------------------------------
   // CYCLE counter

   (* no_implicit_conditions, fire_when_enabled *)
   rule rl_mcycle_incr;
      // Update due to CSRRx    TODO: fix this
      if (rw_mcycle.wget matches tagged Valid .v)
         rg_mcycle <= rg_mcycle + 1;

      // Update due to clock
      else begin
`ifdef EVAL
         // 8-10h at 100MHz
         if (rg_mcycle [41:40] != 2'b11) rg_mcycle <= rg_mcycle + 1;
`else
         rg_mcycle <= rg_mcycle + 1;
`endif
      end
   endrule

   // ----------------------------------------------------------------
   // INSTRET

   (* descending_urgency = "rl_reset_start, rl_upd_minstret_csrrx" *)
   rule rl_upd_minstret_csrrx (rw_minstret.wget matches tagged Valid .v);
      rg_minstret <= v;
      // $display ("%0d: CSR_RegFile_UM.rl_upd_minstret_csrrx: new value is %0d", rg_mcycle, v);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule rl_upd_minstret_incr ((! isValid (rw_minstret.wget)) && pw_minstret_incr);
      rg_minstret <= rg_minstret + 1;
      // $display ("%0d: CSR_RegFile_UM.rl_upd_minstret_incr: new value is %0d", rg_mcycle, rg_minstret + 1);
   endrule

   // ----------------------------------------------------------------
   // Help functions for interface methods

   // ----------------
   // Test if CSR is supported

   function Bool fv_csr_exists (CSR_Addr csr_addr);
      Bool result = (   
                     // Machine mode csrs
                        (csr_addr == csr_addr_mstatus)
                     || (csr_addr == csr_addr_mie)
                     || (csr_addr == csr_addr_mtvec)

                     || (csr_addr == csr_addr_mepc)
                     || (csr_addr == csr_addr_mscratch)
                     || (csr_addr == csr_addr_mcause)
                     || (csr_addr == csr_addr_mtval)
                     || (csr_addr == csr_addr_mip)

                     || (csr_addr == csr_addr_mcycle)
                     || (csr_addr == csr_addr_minstret)
`ifdef RV32
                     || (csr_addr == csr_addr_mcycleh)
                     || (csr_addr == csr_addr_minstreth)
`endif

`ifdef INCLUDE_GDB_CONTROL
                     || (csr_addr == csr_addr_dcsr)
                     || (csr_addr == csr_addr_dpc)
                     || (csr_addr == csr_addr_dscratch0)
                     || (csr_addr == csr_addr_dscratch1)
`endif
         );
      return result;
   endfunction: fv_csr_exists

   // ----------------
   // CSR reads (no side effect)
   // Returns Invalid for invalid CSR addresses or access-mode violations

   function Maybe #(Word) fv_csr_read (CSR_Addr csr_addr);
      Maybe #(Word)  m_csr_value = tagged Invalid;

      case (csr_addr)
         // Machine mode csrs
         csr_addr_misa:       m_csr_value = tagged Valid (misa_to_word (misa));
         csr_addr_mstatus:    m_csr_value = tagged Valid (csr_mstatus.mv_read);
         csr_addr_mie:        m_csr_value = tagged Valid (csr_mie.mv_read);
         csr_addr_mtvec:      m_csr_value = tagged Valid (mtvec_to_word (rg_mtvec));

         csr_addr_mscratch:   m_csr_value = tagged Valid rg_mscratch;
`ifdef ISA_C
         csr_addr_mepc:       m_csr_value = tagged Valid ((misa.c == 1'b1) ? rg_mepc : (rg_mepc & (~ 2)));
`else
         csr_addr_mepc:       m_csr_value = tagged Valid (rg_mepc & (~ 2));
`endif
         csr_addr_mcause:     m_csr_value = tagged Valid (mcause_to_word (rg_mcause));
         csr_addr_mtval:      m_csr_value = tagged Valid rg_mtval;
         csr_addr_mip:        m_csr_value = tagged Valid (csr_mip.mv_read);

         csr_addr_mcycle:    m_csr_value = tagged Valid (truncate (rg_mcycle));
         csr_addr_minstret:  m_csr_value = tagged Valid (truncate (rg_minstret));
`ifdef RV32
         csr_addr_mcycleh:   m_csr_value = tagged Valid (rg_mcycle [63:32]);
         csr_addr_minstreth: m_csr_value = tagged Valid (rg_minstret [63:32]);
`endif

`ifdef INCLUDE_GDB_CONTROL
         csr_addr_dcsr:       begin
                                 Bit #(32) dcsr_nmip_mask = 'b_1000;
                                 Bit #(32) dcsr = (rg_dcsr & (~ dcsr_nmip_mask));
                                 m_csr_value = tagged Valid zeroExtend (dcsr);
                              end
         csr_addr_dpc:        m_csr_value = tagged Valid rg_dpc;
         csr_addr_dscratch0:  m_csr_value = tagged Valid rg_dscratch0;
         csr_addr_dscratch1:  m_csr_value = tagged Valid rg_dscratch1;
`endif

         default: m_csr_value = tagged Invalid;
      endcase

      return m_csr_value;
   endfunction: fv_csr_read

   // ----------------------------------------------------------------
   // CSR writes
   // Returns the "actual value written": many CSRs have WARL/WLRL semantics, i.e., the
   // value attempted to be written is transformed in an implementation-defined way into
   // a value actually written.  In the extreme case of CSRs with hardwired value, the
   // transformation is to ignore the attempted write-value and return the hardwired value.
   // The value returned is conceptually the value you'd read if you did a subsequent CSR read.

   function ActionValue #(CSR_Write_Result) fav_csr_write (CSR_Addr csr_addr, WordXL wordxl);
      actionvalue
         Bool            success = True;
         WordXL          new_csr_value  = ?;
         Maybe #(WordXL) m_new_csr_value2 = tagged Invalid;

         case (csr_addr)
            // Machine mode
            csr_addr_mstatus: begin
               let new_mstatus = MSTATUS_Internal {
                    mie : wordxl[mstatus_mie_bitpos]
                  , mpie: wordxl[mstatus_mpie_bitpos]
               };
               new_csr_value <- csr_mstatus.mav_write (new_mstatus);
               if (verbosity > 1) 
                  $display ("%06d:[D]:%m.mav_csr_write: (csr: mstatus) ", cur_cycle, fshow_mstatus (new_csr_value));
            end
            csr_addr_mie: begin
               let new_mie = MIE_Internal {
                    meie: wordxl[mip_meip_bitpos]
                  , mtie: wordxl[mip_mtip_bitpos]
                  , msie: wordxl[mip_msip_bitpos]
               };
               new_csr_value <- csr_mie.mav_write (new_mie);
            end
            csr_addr_mtvec: begin
               let mtvec     = word_to_mtvec (wordxl);
               new_csr_value = mtvec_to_word (mtvec);
               rg_mtvec     <= mtvec;
            end
            csr_addr_mscratch: begin
               new_csr_value = wordxl;
               rg_mscratch  <= new_csr_value;
            end
            csr_addr_mepc: begin
               new_csr_value = (wordxl & (~ 3));    // mepc [1:0] always zero
               rg_mepc      <= new_csr_value;
            end
            csr_addr_mcause: begin
               let mcause    = word_to_mcause (wordxl);
               new_csr_value = mcause_to_word (mcause);
               rg_mcause    <= mcause;
            end
            csr_addr_mtval:      begin
                                    new_csr_value = wordxl;
                                    rg_mtval     <= new_csr_value;
                                 end
`ifdef RV32
            csr_addr_mcycle:     begin
                                    new_csr_value = wordxl;
                                    rw_mcycle.wset ({ rg_mcycle   [63:32], wordxl });
                                 end
            csr_addr_minstret:   begin
                                    new_csr_value = wordxl;
                                    rw_minstret.wset ({ rg_minstret [63:32], wordxl });
                                 end
            csr_addr_mcycleh:    begin
                                    new_csr_value = wordxl;
                                    rw_mcycle.wset ({ wordxl, rg_mcycle   [31:0] });
                                 end
            csr_addr_minstreth:  begin
                                    new_csr_value = wordxl;
                                    rw_minstret.wset ({ wordxl, rg_minstret [31:0] });
                                 end
`else
            csr_addr_mcycle:     begin
                                    new_csr_value = wordxl;
                                    rw_mcycle.wset (new_csr_value);
                                 end
            csr_addr_minstret:   begin
                                    new_csr_value = wordxl;
                                    rw_minstret.wset (new_csr_value);
                                 end
`endif

`ifdef INCLUDE_GDB_CONTROL
            csr_addr_dcsr:       begin
                                    Bit #(32) new_dcsr
                                    = {rg_dcsr [31:28],   // xdebugver: read-only
                                       rg_dcsr [27:16],   // reserved
                                       wordxl  [15:12],   // ebreakm/s/u,
                                       wordxl  [11:9],    // stepie, stopcount, stoptime
                                       rg_dcsr [8:6],     // cause: read-only
                                       rg_dcsr [5],       // reserved
                                       wordxl  [4],       // mprvn
                                       rg_dcsr [3],       // nmip: read-only
                                       wordxl  [2],       // step
                                       wordxl  [1:0]};    // prv
                                    new_csr_value = zeroExtend (new_dcsr);
                                    rg_dcsr      <= new_dcsr;
                                 end
            csr_addr_dpc:        begin
                                    new_csr_value = wordxl;
                                    rg_dpc       <= new_csr_value;
                                 end
            csr_addr_dscratch0:  begin
                                    new_csr_value = wordxl;
                                    rg_dscratch0 <= new_csr_value;
                                 end
            csr_addr_dscratch1:  begin
                                    new_csr_value = wordxl;
                                    rg_dscratch1 <= new_csr_value;
                                 end
`endif

            default: success = False;
         endcase

         if ((! success) && (verbosity > 1))
            $display ("%06d:[E]:%m.mav_csr_write:CSR-write addr 0x%0h val 0x%0h not successful", cur_cycle,
                      csr_addr, wordxl);

         return CSR_Write_Result {new_csr_value:    new_csr_value,
                                  m_new_csr_value2: m_new_csr_value2};
      endactionvalue
   endfunction: fav_csr_write

   // Access permission
   function Bool fv_access_permitted (CSR_Addr csr_addr, Bool read_not_write);
      Bool exists  = fv_csr_exists (csr_addr);    // Is this CSR implemented?

      Bool priv_ok = True;  // All CSR accessible at this privilege level

      Bool rw_ok = (read_not_write || (csr_addr [11:10] != 2'b11));

      return (exists && priv_ok && rw_ok);
   endfunction: fv_access_permitted

   // ================================================================
   // For debugging

   function Action fa_show_trap_csrs (WordXL ip, WordXL ie,
                                      MCause cause, WordXL status, MTVec tvec,
                                      WordXL epc, WordXL tval);
      action
         $write ("    Trap CSRs ");
         $write (" ip: 0x%0h", ip);
         $write (" ie: 0x%0h", ie);
         $write (" cause:", fshow (cause));
         $display ("");

         $write ("        ");
         $write (" status: 0x%0h", status);
         $write (" tvec: 0x%0h", mtvec_to_word (tvec));
         $write (" epc: 0x%0h", epc);
         $write (" tval: 0x%0h", tval);
         $display ("");
      endaction
   endfunction

   // ================================================================
   // INTERFACE

   // ----------------------------------------------------------------
   // Help functions for interface methods

   // ----------------------------------------------------------------
   // Reset
   interface Server server_reset;
      interface Put request;
         method Action put (Token token);
            rg_state <= RF_RESET_START;

            // This response is placed here, and not in rl_reset_loop, because
            // reset_loop can happen on power-up, where no response is expected.
            f_reset_rsps.enq (?);
         endmethod
      endinterface
      interface Get response;
         method ActionValue #(Token) get if (rg_state == RF_RUNNING);
            let token <- pop (f_reset_rsps);
            return token;
         endmethod
      endinterface
   endinterface

   // CSR read (w.o. side effect)
   method Maybe #(Word) read_csr (CSR_Addr csr_addr);
      return fv_csr_read (csr_addr);
   endmethod

   // CSR write
   method ActionValue #(CSR_Write_Result) mav_csr_write (CSR_Addr csr_addr, WordXL word);
      let result <- fav_csr_write (csr_addr, word);
      return result;
   endmethod

   // Read MSTATUS
   method WordXL read_mstatus;
      return  csr_mstatus.mv_read;
   endmethod

   // CSR Trap actions
   method ActionValue #(Addr) csr_trap_actions (
        WordXL     pc
      , Bool       interrupt    // other interrupt
      , Exc_Code   exc_code
      , WordXL     xtval);

      let cur_mstatus = csr_mstatus.mv_read;
      if (verbosity > 1) begin
         $display ("%06d:[D]:%m.csr_trap_actions:", cur_cycle);
         $display ("    pc 0x%0h  interrupt %0d  exc_code %0d",
                   pc, pack (interrupt), exc_code);

         fa_show_trap_csrs (csr_mip.mv_read, csr_mie.mv_read, rg_mcause,
                            cur_mstatus, rg_mtvec, rg_mepc, rg_mtval);
      end

      let new_priv    = m_Priv_Mode;

      // New MSTATUS value (move MSTATUS.MIE to MSTATUS.MPIE)
      let new_mstatus  = MSTATUS_Internal {
         mpie:cur_mstatus[mstatus_mie_bitpos], mie:1'b0};

      let new_status  <- csr_mstatus.mav_write (new_mstatus);

      let  xcause      = (MCause {interrupt: pack (interrupt), exc_code: exc_code});
      let  is_vectored = (rg_mtvec.mode == VECTORED);
      Addr exc_pc      = (extend (rg_mtvec.base)) << 2;

      rg_mepc    <= pc;
      rg_mcause  <= xcause;
      rg_mtval   <= xtval;

      // Adjust the exception PC if xTVEC mode bits so indicate
      Addr vector_offset = (extend (exc_code)) << 2;
      if (interrupt && is_vectored)
         exc_pc = exc_pc + vector_offset;

      if (verbosity > 1) begin
         $write ("    Return: new pc 0x%0h  ", exc_pc);
         $write (" new mstatus:", fshow_mstatus (new_status));
         $write (" new xcause:", fshow (xcause));
         $write (" new priv %0d", new_priv);
         $display ("");
      end

      return (exc_pc);
   endmethod: csr_trap_actions

   // CSR RET actions (return from exception)
   method ActionValue #(Addr) csr_ret_actions;
      // New MSTATUS value (restore MSTATUS.MIE from MSTATUS.MPIE)
      let cur_mstatus = csr_mstatus.mv_read;
      let new_mstatus  = MSTATUS_Internal {
         mie:cur_mstatus[mstatus_mpie_bitpos], mpie:1'b0};

      csr_mstatus.ma_write (new_mstatus);
`ifdef ISA_C
      WordXL next_pc = rg_mepc & (~1);
`else
      WordXL next_pc = rg_mepc & (~3);
`endif
      return (next_pc);
   endmethod

   // Read MINSTRET
   method Bit #(64) read_csr_minstret;
      return rg_minstret;
   endmethod

   // Increment MINSTRET
   method Action csr_minstret_incr;
      pw_minstret_incr.send;
   endmethod

   // Read MCYCLE
   method Bit #(64) read_csr_mcycle;
      return rg_mcycle;
   endmethod

   // Read MTIME
   method Bit #(64) read_csr_mtime;
      // We use mcycle as a proxy for time
      return rg_mcycle;
   endmethod

   // Read MISA
   method MISA read_misa;
      return misa;
   endmethod

   // Access permission
   method Bool access_permitted (CSR_Addr  csr_addr,  Bool read_not_write);
      return fv_access_permitted (csr_addr, read_not_write);
   endmethod

   // Read MIP
   method WordXL csr_mip_read;
      return csr_mip.mv_read;
   endmethod

   // Interrupts
   method Action m_external_interrupt_req (Bool set_not_clear);
      csr_mip.m_external_interrupt_req  (set_not_clear);
      if ((verbosity > 1) && set_not_clear)
         $display ("%06d:[D]:%m.m_external_interrupt_req: %x"
            , cur_cycle, set_not_clear);
   endmethod

   method Action timer_interrupt_req (Bool set_not_clear);
      csr_mip.m_timer_interrupt_req  (set_not_clear);
      if ((verbosity > 1) && set_not_clear)
         $display ("%06d:[D]:%m.timer_interrupt_req: %x"
            , cur_cycle, set_not_clear);
   endmethod

   method Action software_interrupt_req (Bool set_not_clear);
      csr_mip.m_software_interrupt_req (set_not_clear);
      if ((verbosity > 1) && set_not_clear)
         $display ("%06d:[D]:%m.software_interrupt_req: %x"
            , cur_cycle, set_not_clear);
   endmethod

   method Maybe #(Exc_Code) interrupt_pending;
      return fv_interrupt_pending (csr_mstatus.mv_read,
                                   csr_mip.mv_read,
                                   csr_mie.mv_read);
   endmethod

   // WFI ignores mstatus ies and ideleg regs
   method Bool wfi_resume;
      WordXL mip = csr_mip.mv_read;
      WordXL mie = csr_mie.mv_read;
      return ((mip & mie) != 0);
   endmethod

   // ----------------
   // Methods when Debug Module is present

`ifdef INCLUDE_GDB_CONTROL
   // Read dpc
   method Word read_dpc ();
      return rg_dpc;
   endmethod

   // Update dpc
   method Action write_dpc (Addr pc);
      rg_dpc <= pc;
   endmethod

   // Break should enter Debug Mode
   method Bool dcsr_break_enters_debug (Priv_Mode cur_priv);
      return case (cur_priv)
                m_Priv_Mode: (rg_dcsr [15] == 1'b1);
                s_Priv_Mode: (rg_dcsr [13] == 1'b1);
                u_Priv_Mode: (rg_dcsr [12] == 1'b1);
             endcase;
   endmethod

   // Read dcsr.step
   method Bool read_dcsr_step ();
      return unpack (rg_dcsr [2]);
   endmethod

   // Update 'cause' and 'priv' in DCSR
   method Action write_dcsr_cause_priv (DCSR_Cause  cause, Priv_Mode  priv);
      Bit #(3) b3 = pack (cause);
      rg_dcsr <= { rg_dcsr [31:9], b3, rg_dcsr [5:2], priv };
   endmethod

`endif

   // ----------------
   // Debugging this module

   method Action debug;
      $display ("mstatus = 0x%0h", csr_mstatus.mv_read);
      $display ("mip     = 0x%0h", csr_mip.mv_read);
      $display ("mie     = 0x%0h", csr_mie.mv_read);
   endmethod      
endmodule

// ================================================================

endpackage
