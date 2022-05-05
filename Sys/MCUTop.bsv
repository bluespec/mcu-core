// Copyright (c) 2018-2019 Bluespec, Inc. All Rights Reserved.

package MCUTop;

// ================================================================
// 
// This package defines the interface and implementation of the 
// top-level for the micro-controller (MCU) core. 
//
// This core contains:
//    - BSCore
//    - Optional DM
//    - Optional JTAG TAP interface for DM

// ================================================================
// BSV library imports

import GetPut           :: *;
import ClientServer     :: *;
import Connectable      :: *;
import Clocks           :: *;

// ----------------
// BSV additional libs

// ================================================================
// Project imports

// The core
import BSCore           :: *;
import Near_Mem_IFC     :: *; // for Near_Mem_Fabric_IFC

`ifdef WATCH_TOHOST
import Fabric_Defs      :: *;
`endif

`ifdef INCLUDE_GDB_CONTROL
// The debug module
import BSDebug          :: *;
import Jtag             :: *;
import Giraffe_IFC      :: *;
import DM_CPU_Req_Rsp   :: *;
`endif

// ================================================================
// The BSCore interface

interface MCUTop_IFC;

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
   (* always_ready, always_enabled, prefix=""  *)
   method Action  software_interrupt_req (
      (* port="sw_interrupt" *) Bool set_not_clear);

   (* always_ready, always_enabled, prefix=""  *)
   method Action  timer_interrupt_req (
      (* port="timer_interrupt" *) Bool set_not_clear);

`ifdef Near_Mem_TCM
`ifdef TCM_LOADER
   // connections to loader
   interface Near_Mem_DMA_IFC dma_server;
   (* always_ready *)
   method Bool reset_done;
   (* always_ready, always_enabled *)
   method Action cpu_halt(Bool x);
`endif
`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool  watch_tohost, Fabric_Addr tohost_addr);
   method Fabric_Data mv_tohost_value;
`endif
`endif

   // Debug related sub-interfaces
`ifdef INCLUDE_GDB_CONTROL
   interface Reset ndm_resetn;
   (* prefix="" *)
   interface JTAG_IFC jtag;
`endif

endinterface

// ================================================================

(* synthesize *)
`ifdef INCLUDE_GDB_CONTROL
module mkMCUTop ((*reset="TRST"*) Reset dmi_reset, MCUTop_IFC _ifc);
`else
module mkMCUTop (MCUTop_IFC);
`endif

   let bscore <- mkBSCore;

`ifdef INCLUDE_GDB_CONTROL
   let bsdebug <- mkBSDebug (dmi_reset);
   mkConnection (bsdebug.toCore, bscore.debug);
`endif

   // ================================================================
   // INTERFACE
   // master0 is the instruction memory interface
   // master1 is the data memory interface
`ifndef Near_Mem_TCM
   // CPU IMem to Fabric master interface
   interface Near_Mem_Fabric_IFC master0 = bscore.master0;
`endif

   // CPU DMem to Fabric master interface
   interface Near_Mem_Fabric_IFC master1 = bscore.master1;

   // External interrupts
   method Action m_external_interrupt_req (Bool set_not_clear);
      bscore.m_external_interrupt_req (set_not_clear);
   endmethod

`ifndef MIN_CSR
   method Action s_external_interrupt_req (Bool set_not_clear);
      bscore.s_external_interrupt_req (set_not_clear);
   endmethod
`endif

   // ----------------------------------------------------------------
   // Software and timer interrupt requests from CLINT

   method Action software_interrupt_req (Bool set_not_clear);
      bscore.software_interrupt_req (set_not_clear);
   endmethod

   method Action timer_interrupt_req (Bool set_not_clear);
      bscore.timer_interrupt_req (set_not_clear);
   endmethod


`ifdef Near_Mem_TCM
`ifdef TCM_LOADER
   interface dma_server = bscore.dma_server;
   method Action cpu_halt (Bool x) = bscore.cpu_halt (x);
   method reset_done = bscore.reset_done;
`endif

`ifdef WATCH_TOHOST
   // For ISA tests: watch memory writes to <tohost> addr
   method Action set_watch_tohost (Bool  watch_tohost, Fabric_Addr tohost_addr);
      bscore.set_watch_tohost (watch_tohost, tohost_addr);
   endmethod

   method Fabric_Data mv_tohost_value = bscore.mv_tohost_value;
`endif
`endif

`ifdef INCLUDE_GDB_CONTROL
   interface Reset ndm_resetn = bsdebug.ndm_resetn;
   interface JTAG_IFC jtag = bsdebug.jtag;
`endif

endmodule

// ================================================================

endpackage
