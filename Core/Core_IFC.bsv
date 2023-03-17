// Copyright (c) 2018-2021 Bluespec, Inc. All Rights Reserved.

package Core_IFC;

// ================================================================
// This package defines the interface of a Core module which connects
// to the SoC socket
//
// Macros Supported:
//    MIN_CSR
//    Near_Mem_TCM
//    TCM_BACK_DOOR (assumes Near_Mem_TCM)
//    FABRIC_AXI4 OR FABRIC_AHBL OR FABRIC_APB
//    INCLUDE_GDB_CONTROL
//    INCLUDE_TANDEM_VERIF
//    MEM_TOHOST
// ================================================================
// BSV library imports

import Vector        :: *;
import GetPut        :: *;
import ClientServer  :: *;

// ================================================================
// Project imports

import Near_Mem_IFC     :: *;    // For Wd_{Id,Addr,Data,User}_Dma

import ISA_Decls        :: *;
import CPU_Globals      :: *;

// Main fabric
import AXI4_Types       :: *;
import Fabric_Defs      :: *;

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

`ifdef ISA_X
import XTypes           :: *;
`endif

// ================================================================
// The Core interface

interface Core_IFC;

   // ----------------------------------------------------------------
   // Soft reset
   // 'Bool' is initial 'running' state

   interface Server #(Bool, Bool)  cpu_reset_server;

   // ----------------------------------------------------------------
   // AXI4 Fabric interfaces

`ifndef Near_Mem_TCM
   // CPU IMem to Fabric master interface. Present only in cache-based
   // Near-Mem systems
   interface Near_Mem_Fabric_IFC m1;
`endif

   // The dmem system interface is APB/AHBL/AXI4. Although APB/AHBL are only
   // meant for the TCM, these definitions would hold for cache-based near-mems
   // as well.
   interface Near_Mem_Fabric_IFC m0;

   // ----------------------------------------------------------------
   // Interface to optional 'system DMAC'
   // When TCMs are present this will serve as a back-door to access TCMs
   // If a DM is present then these channels are replaced with the SB
   // access interface to the near-mem
`ifdef Near_Mem_TCM
`ifdef TCM_LOADER
   interface Server #(SB_Sys_Req, Bool)  dma_server;
`endif
`endif

`ifdef ISA_X
   // Coprocessor extension interface
   interface XCPU_Ifc accel_ifc;
`endif

   // ----------------
   // External interrupts

   (* always_ready, always_enabled, prefix=""  *)
   method Action  m_external_interrupt_req (
      (* port="ext_interrupt" *) Bool set_not_clear);

`ifndef MIN_CSR
   (* always_ready, always_enabled, prefix=""  *)
   method Action  s_external_interrupt_req (
      (* port="s_ext_interrupt" *) Bool set_not_clear);

   // ----------------------------------------------------------------
   // Non-maskable interrupt request

   (* always_ready, always_enabled, prefix=""  *)
   method Action nmi_req (
      (* port="nmi" *) Bool set_not_clear);
`endif

   // ----------------
   // Software and timer interrupts (from CLINT)

   (* always_ready, always_enabled, prefix=""  *)
   method Action software_interrupt_req (
      (* port="sw_interrupt" *) Bool set_not_clear);

   (* always_ready, always_enabled, prefix=""  *)
   method Action timer_interrupt_req (
      (* port="timer_interrupt" *) Bool set_not_clear);

   // ----------------------------------------------------------------
   // Optional Debug Module interfaces

`ifdef INCLUDE_GDB_CONTROL
   // ----------------
   // Debug Module Interface (facing external debug module)
   interface Server #(DM_Sys_Req, DM_Sys_Rsp) debug;
`endif
   // ----------------------------------------------------------------
   // Misc. control and status

`ifndef SYNTHESIS
   // ----------------
   // Debugging: set core's verbosity
   (* always_ready *)
   method Action  set_verbosity (Bit #(2)  verbosity);
   (* always_ready *)
   method Action  ma_close_logs;

   // ----------------
   // For ISA tests: watch memory writes to <tohost> addr
`ifdef MEM_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Fabric_Addr tohost_addr);
`endif
`endif

endinterface

// ================================================================

endpackage
