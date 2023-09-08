// Copyright (c) 2013-2020 Bluespec, Inc. All Rights Reserved

package Core_Map;

// ================================================================
// This module defines the overall 'address map' of elements
// inside the core. This package is derived from SoC_Map

// ***** WARNING! WARNING! WARNING! *****

// During system integration, this address map should be identical to
// the system interconnect settings (e.g., routing of requests between
// masters and slaves).  This map is also needed by software so that
// it knows how to address various IPs.

// This module contains no state; it just has constants, and so can be
// freely instantiated at multiple places in the SoC module hierarchy
// at no hardware cost.  It allows this map to be defined in one
// place and shared across the SoC.

// ================================================================
// Bluespec library imports

// None

// ================================================================
// Project imports

import Fabric_Defs   :: *; // Only for type Fabric_Addr

`ifdef Near_Mem_TCM
import TCM_Decls     :: *;
`endif

// ================================================================
// Interface and module for the address map

interface Core_Map_IFC;
`ifdef Near_Mem_TCM
`ifdef TCM_DP_SINGLE_MEM
   (* always_ready *)   method  Fabric_Addr  m_tcm_addr_base;
   (* always_ready *)   method  Fabric_Addr  m_tcm_addr_size;
   (* always_ready *)   method  Fabric_Addr  m_tcm_addr_lim;
   (* always_ready *)   method  Bool         m_is_tcm_addr (Fabric_Addr addr);
`else
   (* always_ready *)   method  Fabric_Addr  m_itcm_addr_base;
   (* always_ready *)   method  Fabric_Addr  m_itcm_addr_size;
   (* always_ready *)   method  Fabric_Addr  m_itcm_addr_lim;
   (* always_ready *)   method  Bool         m_is_itcm_addr (Fabric_Addr addr);

   (* always_ready *)   method  Fabric_Addr  m_dtcm_addr_base;
   (* always_ready *)   method  Fabric_Addr  m_dtcm_addr_size;
   (* always_ready *)   method  Fabric_Addr  m_dtcm_addr_lim;
   (* always_ready *)   method  Bool         m_is_dtcm_addr (Fabric_Addr addr);
`endif   // ifndef TCM_DP_SINGLE_MEM
`endif

   (* always_ready *)   method  Fabric_Addr m_pc_reset_value;
   (* always_ready *)   method  Fabric_Addr m_mtvec_reset_value;

`ifndef MIN_CSR
   // Non-maskable interrupt vector
   (* always_ready *)   method  Fabric_Addr m_nmivec_reset_value;
`endif
endinterface

// ================================================================

(* synthesize *)
module mkCore_Map (Core_Map_IFC);

`ifdef Near_Mem_TCM
   // ----------------------------------------------------------------
   // Tightly-coupled memory ('TCM'; optional)
   // When TCMs are enabled, the iTCM address base is at the address usually
   // used for the mem0_controller. This avoids changing the start location
   // of bare-metal programs.
   //
   // The "main" memory now starts from 0x1000_0000 later, effectively
   // leaving 256 MB for the two TCMs
   //
`ifdef TCM_DP_SINGLE_MEM
   // Unified TCMs are of the same size, controlled by a
   // single tcm_addr_size value.
   Fabric_Addr tcm_addr_base = 'h_C000_0000;
   Fabric_Addr tcm_addr_size = fromInteger (bytes_per_TCM);
   Fabric_Addr tcm_addr_lim  = tcm_addr_base + tcm_addr_size;

   function Bool fn_is_tcm_addr (Fabric_Addr addr);
      Bit #(TSub #(Wd_Addr, TCM_Addr_LSB)) tcm_base_msb = truncate (
         tcm_addr_base >> tcm_addr_lsb);
      Bit #(TSub #(Wd_Addr, TCM_Addr_LSB)) addr_msb = truncate (
         addr >> tcm_addr_lsb);
      return (tcm_base_msb == addr_msb);
   endfunction
`else

   Fabric_Addr itcm_addr_base = 'h_C000_0000;
   Fabric_Addr itcm_addr_size = fromInteger (bytes_per_ITCM);
   Fabric_Addr itcm_addr_lim  = itcm_addr_base + itcm_addr_size;

   function Bool fn_is_itcm_addr (Fabric_Addr addr);
      Bit #(TSub #(Wd_Addr, ITCM_Addr_LSB)) tcm_base_msb = truncate (
         itcm_addr_base >> itcm_addr_lsb);
      Bit #(TSub #(Wd_Addr, ITCM_Addr_LSB)) addr_msb = truncate (
         addr >> itcm_addr_lsb);
      return (tcm_base_msb == addr_msb);
   endfunction

   Fabric_Addr dtcm_addr_base = 'h_C800_0000;
   Fabric_Addr dtcm_addr_size = fromInteger (bytes_per_DTCM);
   Fabric_Addr dtcm_addr_lim  = dtcm_addr_base + dtcm_addr_size;

   function Bool fn_is_dtcm_addr (Fabric_Addr addr);
      Bit #(TSub #(Wd_Addr, DTCM_Addr_LSB)) tcm_base_msb = truncate (
         dtcm_addr_base >> dtcm_addr_lsb);
      Bit #(TSub #(Wd_Addr, DTCM_Addr_LSB)) addr_msb = truncate (
         addr >> dtcm_addr_lsb);
      return (tcm_base_msb == addr_msb);
   endfunction
`endif   // ifndef TCM_DP_SINGLE_MEM
`else
   Fabric_Addr mem_addr_base = 'h_C000_0000;
   Fabric_Addr mem_addr_size = 'h_1000_0000; // Arbitrarily set at 256 MB
   Fabric_Addr mem_addr_lim  = 'h_D000_0000;
`endif   // ifndef Near_Mem_TCM

   // ----------------------------------------------------------------
   // PC, MTVEC and NMIVEC reset values
`ifdef Near_Mem_TCM
`ifdef TCM_DP_SINGLE_MEM
   Fabric_Addr pc_reset_value     = tcm_addr_base;
   Fabric_Addr mtvec_reset_value  = tcm_addr_base; // On a trap act like reset
`ifndef MIN_CSR
   Fabric_Addr nmivec_reset_value = tcm_addr_base; // On a NMI act like reset
`endif
`else
   Fabric_Addr pc_reset_value     = itcm_addr_base;
   Fabric_Addr mtvec_reset_value  = itcm_addr_base; // On a trap act like reset
`ifndef MIN_CSR
   Fabric_Addr nmivec_reset_value = itcm_addr_base; // On a NMI act like reset
`endif
`endif   // ifndef TCM_DP_SINGLE_MEM
`else
   // WARNING: If disabling TCMs, ensure that memory model exists in SoC
   Fabric_Addr pc_reset_value     = mem_addr_base;
   Fabric_Addr mtvec_reset_value  = mem_addr_base; // On a trap act like reset
`ifndef MIN_CSR
   Fabric_Addr nmivec_reset_value = mem_addr_base; // On a NMI act like reset
`endif
`endif

   // ================================================================
   // INTERFACE

`ifdef Near_Mem_TCM
`ifdef TCM_DP_SINGLE_MEM
   method  Fabric_Addr  m_tcm_addr_base = tcm_addr_base;
   method  Fabric_Addr  m_tcm_addr_size = tcm_addr_size;
   method  Fabric_Addr  m_tcm_addr_lim  = tcm_addr_lim;
   method  Bool  m_is_tcm_addr (Fabric_Addr addr) = fn_is_tcm_addr (addr);
`else
   method  Fabric_Addr  m_itcm_addr_base = itcm_addr_base;
   method  Fabric_Addr  m_itcm_addr_size = itcm_addr_size;
   method  Fabric_Addr  m_itcm_addr_lim  = itcm_addr_lim;
   method  Bool  m_is_itcm_addr (Fabric_Addr addr) = fn_is_itcm_addr (addr);

   method  Fabric_Addr  m_dtcm_addr_base = dtcm_addr_base;
   method  Fabric_Addr  m_dtcm_addr_size = dtcm_addr_size;
   method  Fabric_Addr  m_dtcm_addr_lim  = dtcm_addr_lim;
   method  Bool  m_is_dtcm_addr (Fabric_Addr addr) = fn_is_dtcm_addr (addr);
`endif   // ifndef TCM_DP_SINGLE_MEM
`endif

   method  Fabric_Addr  m_pc_reset_value     = pc_reset_value;
   method  Fabric_Addr  m_mtvec_reset_value  = mtvec_reset_value;
`ifndef MIN_CSR
   method  Fabric_Addr  m_nmivec_reset_value = nmivec_reset_value;
`endif
endmodule

endpackage
