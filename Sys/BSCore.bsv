// Copyright (c) 2018-2019 Bluespec, Inc. All Rights Reserved.

package BSCore;

// ================================================================
// This package servers as the top-level of the MCU Core
//
// ================================================================
// BSV library imports

import Vector           :: *;
import FIFO             :: *;
import GetPut           :: *;
import ClientServer     :: *;
import Connectable      :: *;
import Clocks           :: *;

// ----------------
// BSV additional libs

import GetPut_Aux       :: *;
import Semi_FIFOF       :: *;

// ================================================================
// Project imports

// The basic core
import ISA_Decls        :: *;
import CPU_Globals      :: *;
import Core_IFC         :: *;
import Core             :: *;
import Near_Mem_IFC     :: *; // for Near_Mem_Fabric_IFC

// Main Fabric
import Fabric_Defs      :: *;

`ifdef FABRIC_AXI4
import AXI4_Types       :: *;
import AXI4_Fabric      :: *;
`endif

`ifdef FABRIC_AHBL
import AHBL_Types       :: *;
import AHBL_Defs        :: *;
`endif

`ifdef FABRIC_APB
import APB_Types        :: *;
import APB_Defs         :: *;
`endif

`ifdef INCLUDE_GDB_CONTROL
import Debug_Interfaces :: *;
`endif

import DM_CPU_Req_Rsp   :: *;   // for SB_Sys_Req

`ifdef TCM_LOADER
import AXI4_Deburster   :: *;
import Loader_AXI4_Adapter :: *;
`endif

`ifdef ISA_X
import XTypes           :: *;
import XCatalyst        :: *;
`endif

import Cur_Cycle        :: *;

// ================================================================
// Constant: cycles to hold SoC in reset for ndm reset:

UInt#(6) ndm_interval = 20;
UInt#(6) por_interval = 20;

// ================================================================
// The BSCore interface

interface BSCore_IFC;

   // ----------------------------------------------------------------
   // Core CPU interfaces
`ifndef Near_Mem_TCM
   // CPU IMem to Fabric master interface
   interface Near_Mem_Fabric_IFC master0;
`endif

   // CPU DMem (incl. I/O) to Fabric master interface
   interface Near_Mem_Fabric_IFC master1;

   // ----------------
   // External interrupts
   (* always_ready, always_enabled, prefix="" *)
   method Action  m_external_interrupt_req (
      (* port="ext_interrupt" *) Bool set_not_clear);

`ifndef MIN_CSR
   (* always_ready, always_enabled, prefix=""  *)
   method Action  s_external_interrupt_req (
      (* port="s_ext_interrupt" *) Bool set_not_clear);
`endif

   // ----------------
   // Software and timer interrupts (from CLINT)
   (* always_ready, always_enabled, prefix="" *)
   method Action  software_interrupt_req (
      (* port="sw_interrupt" *) Bool set_not_clear);

   (* always_ready, always_enabled, prefix="" *)
   method Action  timer_interrupt_req (
      (* port="timer_interrupt" *) Bool set_not_clear);

`ifdef INCLUDE_GDB_CONTROL
   interface Server #(DM_Sys_Req, DM_Sys_Rsp) debug;
`endif

`ifdef Near_Mem_TCM
`ifdef TCM_LOADER
   interface Near_Mem_DMA_IFC dma_server;
   (* always_ready *)
   method Bool reset_done;
   (* always_ready, always_enabled *)
   method Action cpu_halt(Bool x);
`endif
`endif


`ifndef SYNTHESIS
   // ----------------
   // Debugging: set core's verbosity
   method Action  set_verbosity (Bit #(2)  verbosity);
`endif

endinterface

// ================================================================

(* synthesize *)
module mkBSCore (BSCore_IFC);
   let clk <- exposeCurrentClock;
   // Reset this by default reset, so core is reset by both default and ndm
   // Keep reset asserted for 2 cycles after deassertion of default reset
   // Assert reset when default reset is asserted (True)
   let ndmIfc <- mkReset(2, True, clk);
   let coreRSTN = ndmIfc.new_rst;

   // Core: CPU + Near_Mem_IO (CLINT) + PLIC + Debug module (optional) + TV (optional)
   Core_IFC::Core_IFC core <- mkCore(reset_by coreRSTN);

   // ================================================================
   // Tie-offs

`ifndef MIN_CSR
   // Tie-offs
   rule rl_always (True);
      // Non-maskable interrupt request.
      core.nmi_req (False);
   endrule
`endif

   // ================================================================
   // Reset on startup, and also on NDM reset from Debug Module
   // NDM reset from Debug Module = "non-debug-module-reset"
   //                             = reset all except Debug Module

   Reg #(Bool)          rg_once       <- mkReg (False); // also set False by ndmreset
   Reg #(Bool)          rg_reset_done <- mkReg (False);
   Reg #(Bool)          rg_last_cpuh  <- mkReg (False);

   // To support an external loader to reset and halt the CPU
   // Only used when the TCM_LOADER is enabled
   Reg #(Maybe #(Bool)) rg_ldr_reset  <- mkReg (tagged Invalid);

`ifdef INCLUDE_GDB_CONTROL
   Reg #(UInt #(6))     rg_ndm_count <- mkReg (0);

   rule decNdmCountRl (rg_ndm_count != 0);
      rg_ndm_count <= rg_ndm_count -1;
      ndmIfc.assertReset();
   endrule
`endif

   // The Catalyst accelerator core
`ifdef ISA_X
   // shares the same reset as the core (PoR or NDMReset)
   XCatalyst_IFC catalyst <- mkXCatalyst (reset_by coreRSTN);
`endif


   let coreInReset <- isResetAsserted(reset_by coreRSTN);

   // Reset the core -- currently fires on default reset
   rule rl_once (! rg_once && ! coreInReset);
      Bool running = True;
      if (rg_ldr_reset matches tagged Valid False)
	 running = False;
      rg_ldr_reset <= Invalid;
      core.cpu_reset_server.request.put (running);
`ifdef ISA_X
      catalyst.server_reset.request.put (?);
`endif
      // TODO: maybe set rg_ndm_count if debug_module present?
      rg_once <= True;
      $display ("%06d:[D]:%m.rl_once: PoR to Core: (running ",
         cur_cycle, fshow (running), ")");
   endrule

`ifdef TCM_LOADER
   (*descending_urgency="rl_once, cpu_halt"*)
`endif
   rule rl_reset_response;
      let running <- core.cpu_reset_server.response.get;
`ifdef ISA_X
      let xrsp <- catalyst.server_reset.response.get;
`endif

`ifdef INCLUDE_GDB_CONTROL
      // wait for end of ndm_interval:
      when (rg_ndm_count == 0, noAction);
`endif
      rg_reset_done <= True;
   endrule

`ifdef TCM_LOADER
   Loader_AXI4_Adapter_IFC loader_adapter <- mkLoader_AXI4_Adapter (
      core.dma_server);

   AXI4_Deburster_IFC #(
      Wd_Id, Wd_Addr, Wd_Data, Wd_User) deburstr <- mkAXI4_Deburster;
   mkConnection (deburstr.to_slave, loader_adapter.axi);
`endif

`ifdef ISA_X
   // --------
   // memory (Catalyst initiates, CPU serves)
   rule rl_xmem_req;
      let req <- catalyst.x_mem.request.get ();
      core.accel_ifc.x_mem.request.put (X_M_Req {write: req.write,
						 address: req.address,
						 wdata: req.wdata,
						 size: req.size });
   endrule

   rule rl_xmem_rsp;
      let rsp <- core.accel_ifc.x_mem.response.get ();
      catalyst.x_mem.response.put (C_M_Rsp {rdata: rsp.rdata,
					     write: rsp.write,
					     err:   rsp.err });
   endrule

   // --------
   // command (CPU initiates, Catalyst serves)
   rule rl_xcmd_req;
      let req <- core.accel_ifc.x_compute.request.get ();
      catalyst.x_compute.request.put (req);
   endrule

   rule rl_xcmd_rsp;
      let rsp <- catalyst.x_compute.response.get ();
      core.accel_ifc.x_compute.response.put (rsp);
   endrule
`endif

   // ================================================================
   // INTERFACE
   // core.m1 is the instruction memory interface and becomes master0
   // core.m0 is the data memory interface and becomes master1
`ifndef Near_Mem_TCM
   // CPU IMem to Fabric master interface
   interface Near_Mem_Fabric_IFC master0 = core.m1;
`endif

   // CPU DMem to Fabric master interface
   interface Near_Mem_Fabric_IFC master1 = core.m0;

   // External interrupts
   method Action m_external_interrupt_req (Bool set_not_clear);
      core.m_external_interrupt_req (set_not_clear);
   endmethod

`ifndef MIN_CSR
   method Action s_external_interrupt_req (Bool set_not_clear);
      core.s_external_interrupt_req (set_not_clear);
   endmethod
`endif

   // ----------------------------------------------------------------
   // Software and timer interrupt requests from CLINT

   method Action software_interrupt_req (Bool set_not_clear);
      core.software_interrupt_req (set_not_clear);
   endmethod

   method Action timer_interrupt_req (Bool set_not_clear);
      core.timer_interrupt_req (set_not_clear);
   endmethod


`ifdef INCLUDE_GDB_CONTROL
   interface debug = core.debug;
`endif

`ifdef Near_Mem_TCM
`ifdef TCM_LOADER
   interface dma_server = deburstr.from_master;
   method Action cpu_halt (x);
      if (x != rg_last_cpuh && !isValid(rg_ldr_reset)) begin
	 rg_ldr_reset <= tagged Valid (!x); // value is "running"
	 rg_once <= False;
	 rg_last_cpuh <= x;
	 rg_reset_done <= False;
	 if (!x) $display("Trace starting");
      end
   endmethod
   method reset_done = rg_reset_done;
`endif
`endif

   // ----------------------------------------------------------------
   // Misc. control and status

`ifndef SYNTHESIS
   method Action  set_verbosity (Bit #(2)  verbosity);
      core.set_verbosity (verbosity);
   endmethod
`endif

endmodule

// ================================================================

endpackage
