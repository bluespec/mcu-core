// Copyright (c) 2016-2021 Bluespec, Inc. All Rights Reserved

// Macros Supported:
//    INCLUDE_GDB_CONTROL
//    INCLUDE TANDEM_VERIF
//    MIN_CSR
//    Near_Mem_TCM
//       FABRIC_AXI4 or FABRIC_AHBL or FABRIC_APB
//       WATCH_TOHOST
//    INCLUDE_DMEM_SLAVE

package CPU_IFC;

// ================================================================
// BSV library imports

import GetPut       :: *;
import ClientServer :: *;

// ================================================================
// Project imports

import ISA_Decls       :: *;

import AXI4_Types  :: *;
import Fabric_Defs :: *;

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

import DM_CPU_Req_Rsp    :: *;   // for SB_Sys_Req

`ifdef INCLUDE_TANDEM_VERIF
import TV_Info         :: *;
`endif

import Near_Mem_IFC :: *;    // For Wd_Id/Addr/Data/User_Dma/Near_Mem_IFC

// ================================================================
// CPU interface

interface CPU_IFC;
   // ----------------
   // SoC fabric connections
`ifdef Near_Mem_TCM     // TCM based Near Mem

   // Fabric side (MMIO initiator interface)
   interface Near_Mem_Fabric_IFC dmem_master;
   
`else                   // Cache-based Near Mem
   // IMem to Fabric master interface is present in all cases except when a ITCM is present
   interface Near_Mem_Fabric_IFC imem_master;

   // Fabric master interface to memory
   interface Near_Mem_Fabric_IFC  mem_master;
`endif

    // DMA and debug interfaces
`ifdef INCLUDE_GDB_CONTROL
   // AXI4 DMA target interface (for backdoor loading of TCMs in debug mode)
   interface Server #(SB_Sys_Req, SB_Sys_Rsp) dbg_server;
`endif
`ifdef Near_Mem_TCM
`ifdef TCM_LOADER
   // ----------------
   // Interface to 'DMA' port for TCM loading
   interface Server #(SB_Sys_Req, Bool) dma_server;
`endif
`endif


   // ----------------
   // External interrupts

   (* always_ready, always_enabled *)
   method Action  m_external_interrupt_req (Bool set_not_clear);

`ifndef MIN_CSR
   (* always_ready, always_enabled *)
   method Action  s_external_interrupt_req (Bool set_not_clear);
`endif

   // ----------------
   // Software and timer interrupts (from Near_Mem_IO/CLINT)

   (* always_ready, always_enabled *)
   method Action  software_interrupt_req (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action  timer_interrupt_req    (Bool set_not_clear);

`ifndef MIN_CSR
   // ----------------
   // Non-maskable interrupt

   (* always_ready, always_enabled *)
   method Action  nmi_req (Bool set_not_clear);
`endif

   // ----------------
   // Optional interface to Tandem Verifier

`ifdef INCLUDE_TANDEM_VERIF
   interface Get #(Trace_Data)  trace_data_out;
`endif

   // ----------------
   // Optional interface to Debug Module

`ifdef INCLUDE_GDB_CONTROL
   interface CPU_DM_Ifc debug;
`else
   // Reset
   interface Server #(Bool, Bool)  hart_reset_server;
`endif

   // ----------------------------------------------------------------
   // Misc. control and status

   // ----------------
   // Set core's verbosity
   (* always_ready *)
   method Action set_verbosity (Bit #(2)  verbosity);

`ifdef Near_Mem_TCM
   // ----------------
   // For ISA tests: watch memory writes to <tohost> addr
`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Fabric_Addr tohost_addr);
   method Fabric_Data mv_tohost_value;
`endif
`endif

endinterface

// ================================================================

endpackage
