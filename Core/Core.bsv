// Copyright (c) 2018-2021 Bluespec, Inc. All Rights Reserved.

package Core;

// ================================================================
// This package defines the CPU socket for the MCUx class of SoC:
//     Core_IFC
//     mkCore #(Core_IFC)
//
// mkCore instantiates:
//    - Magritte CPU, including:
//       * Tiny-TCM based Near_Mem
//       * 1 external, 1 timer and 1 sw interrupt lines
//       * 1 x AXI4 Master interfaces
//    - Optional Tandem Verification trace stream output interface
//    - Optional custom interface to the RISC-V DM
//    - Optional DM Triage Block
//
// Macros Supported:
//    MIN_CSR
//    Near_Mem_TCM
//    TCM_LOADER (assumes Near_Mem_TCM)
//    FABRIC_AXI4 OR FABRIC_AHBL OR FABRIC_APB
//    INCLUDE_GDB_CONTROL
//    INCLUDE_TANDEM_VERIF
//    WATCH_TOHOST
// ================================================================
// BSV library imports

import Vector        :: *;
import FIFOF         :: *;
import GetPut        :: *;
import ClientServer  :: *;
import Connectable   :: *;

// ----------------
// BSV additional libs

import Cur_Cycle  :: *;
import GetPut_Aux :: *;

// ================================================================
// Project imports

// Main fabric
import AXI4_Types   :: *;
import AXI4_Fabric  :: *;
import Fabric_Defs  :: *;    // for Wd_Id, Wd_Addr, Wd_Data, Wd_User

`ifdef INCLUDE_GDB_CONTROL
import Debug_Interfaces  :: *;
import Debug_Triage      :: *;
`endif

`ifdef ISA_X
import XTypes           :: *;
`endif

import DM_CPU_Req_Rsp    :: *;   // for SB_Sys_Req

import Core_IFC          :: *;
import CPU_IFC           :: *;
import CPU               :: *;

import Near_Mem_IFC      :: *;    // For Near_Mem_DMA_IFC

// ================================================================
// The Core module

(* synthesize *)
module mkCore (Core_IFC);

   // ================================================================
   // STATE

   // The CPU
   // CPU resets after por are controlled by the reset server.
   CPU_IFC  cpu <- mkCPU;

   // Reset requests from SoC and responses to SoC
   // 'Bool' is 'running' state
   FIFOF #(Bool) f_reset_reqs <- mkFIFOF;
   FIFOF #(Bool) f_reset_rsps <- mkFIFOF;

   // ================================================================
   // RESET
   // There are two sources of reset requests to the CPU: externally
   // from the SoC and, optionally, the DM.  When both requestors are
   // present (i.e., DM is present), we merge the reset requests into
   // the CPU, and we remember which one was the requestor in
   // f_reset_requestor, so that we know whome to respond to.

   Bit #(1) reset_requestor_dm  = 0;
   Bit #(1) reset_requestor_soc = 1;
   FIFOF #(Bit #(1)) f_reset_requestor <- mkFIFOF;
`ifdef INCLUDE_GDB_CONTROL
   Server #(Bool, Bool)  hart_reset_server = cpu.debug.hart_reset_server;
`else
   Server #(Bool, Bool)  hart_reset_server = cpu.hart_reset_server;
`endif

   // Reset-hart0 request from SoC
   rule rl_cpu_hart0_reset_from_soc_start;
      let running <- pop (f_reset_reqs);

      hart_reset_server.request.put (running);   // CPU

      // Remember the requestor, so we can respond to it
      f_reset_requestor.enq (reset_requestor_soc);
      $display ("%06d:[D]:%m.rl_cpu_hart0_reset_from_soc_start", cur_cycle);
   endrule


   // This interface wrapper is the point of interaction of the Triage block with
   // the CPU's reset server. This wrapper is necessary as there can be requests
   // to the reset server which originates from the SoC as well. The response
   // therefore has to be sent to the correct source and this wrapper acts as the
   // shim for the reset requests originating from the DM
`ifdef INCLUDE_GDB_CONTROL
   // Reset-hart0 from Debug Module
   Server #(Bool, Bool) dm_reset_server = ( interface Server;
      interface Put request;
	 method Action put(running);
	    hart_reset_server.request.put (running);    // CPU

	    // Remember the requestor, so we can respond to it
	    f_reset_requestor.enq (reset_requestor_dm);
	    $display ("%06d:[D]:%m.rl_cpu_hart0_reset_from_dm_start", cur_cycle);
	 endmethod
      endinterface
      interface Get response;
	 method ActionValue#(Bool) get() if (f_reset_requestor.first == reset_requestor_dm);
	    let running <- hart_reset_server.response.get;     // CPU

	    f_reset_requestor.deq;
	    $display ("%06d:[D]:%m.rl_cpu_hart0_reset_complete", cur_cycle);
	    return running;
	 endmethod
      endinterface
   endinterface );
`endif

   rule rl_cpu_hart0_reset_complete  (f_reset_requestor.first == reset_requestor_soc);
      let running <- hart_reset_server.response.get;     // CPU

      f_reset_rsps.enq (running);
      f_reset_requestor.deq;
      $display ("%06d:[D]:%m.rl_cpu_hart0_reset_complete", cur_cycle);
   endrule

   // ================================================================
   // Other CPU/DM/TV connections
   // (depends on whether DM, TV or both are present)

`ifdef INCLUDE_GDB_CONTROL
   // ----------------------------------------------------------------
   // Instantiate Debug Triage to connect DM sys requests to different
   // targets inside the hart

   // A dummy mem server to service all SB requests. Temporary to test DM
   // connection feature before proceeding with NM integration
   let dm_stub <- mkDebugTriage(
      dm_reset_server
    , cpu.debug.hart_server_run_halt
    , cpu.debug.gpr_dbg_server
    , cpu.debug.csr_dbg_server
    , cpu.mem_dbg_server
 );
`endif

   // ================================================================
   // INTERFACE

   // Reset interface
   interface Server cpu_reset_server = toGPServer (f_reset_reqs, f_reset_rsps);

   // ----------------------------------------------------------------
   // AXI4 Fabric interfaces

`ifndef Near_Mem_TCM
   // IMem to Fabric master interface
   interface m1 = cpu.imem_master;
`endif

   // DMem to Fabric master interface
   interface m0 = cpu.dmem_master;

   // ----------------------------------------------------------------
   // External interrupt sources

   method Action m_external_interrupt_req (Bool set_not_clear);
      cpu.m_external_interrupt_req (set_not_clear);
   endmethod

`ifndef MIN_CSR
   method Action s_external_interrupt_req (Bool set_not_clear);
      cpu.s_external_interrupt_req (set_not_clear);
   endmethod

   // ----------------------------------------------------------------
   // Non-maskable interrupt request

   method Action nmi_req (Bool set_not_clear);
      cpu.nmi_req (set_not_clear);
   endmethod
`endif

   // ----------------------------------------------------------------
   // Software and timer interrupt requests from CLINT

   method Action software_interrupt_req (Bool set_not_clear);
      cpu.software_interrupt_req (set_not_clear);
   endmethod

   method Action timer_interrupt_req (Bool set_not_clear);
      cpu.timer_interrupt_req (set_not_clear);
   endmethod

   // ----------------------------------------------------------------
   // Optional direct memory and debug interfaces

`ifdef INCLUDE_GDB_CONTROL
   // ----------------
   // DMI (Debug Module Interface) facing remote debugger
   interface Server debug = dm_stub.server;
`endif

`ifdef Near_Mem_TCM
`ifdef TCM_LOADER
   // ----------------
   // Interface to 'DMA' port for TCM loading
   interface Server dma_server = cpu.dma_server;
`endif
`endif

`ifdef ISA_X
   interface XCPU_Ifc accel_ifc = cpu.accel_ifc;
`endif

   // ----------------------------------------------------------------
   // Misc. control and status

`ifndef SYNTHESIS
   method Action  set_verbosity (Bit #(2)  verbosity);
      cpu.set_verbosity (verbosity);
   endmethod
`endif

   // ----------------
   // For ISA tests: watch memory writes to <tohost> addr

`ifdef Near_Mem_TCM
`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Fabric_Addr tohost_addr);
      cpu.set_watch_tohost (watch_tohost, tohost_addr);
   endmethod

   method Fabric_Data mv_tohost_value = cpu.mv_tohost_value;
`endif
`endif

endmodule: mkCore

`ifdef INCLUDE_GDB_CONTROL
(* synthesize *)
module mkDummy_Mem_Server (Server #(SB_Sys_Req, SB_Sys_Rsp));
   FIFOF #(SB_Sys_Req) ff_dm_sys_req <- mkFIFOF;
   FIFOF #(SB_Sys_Rsp) ff_dm_sys_rsp <- mkFIFOF;

   rule rl_req;
      let req = ff_dm_sys_req.first;
      ff_dm_sys_req.deq;
      ff_dm_sys_rsp.enq (
         SB_Sys_Rsp {rdata: ?, read_not_write: req.read_not_write, err: False});
   endrule

   interface Put request = toPut (ff_dm_sys_req);
   interface Get response = toGet (ff_dm_sys_rsp);
endmodule
`endif

endpackage
