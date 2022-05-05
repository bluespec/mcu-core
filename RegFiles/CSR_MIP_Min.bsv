// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

package CSR_MIP_Min;

// ================================================================
// CSR (Control and Status Register) Register MIP

// ================================================================
// BSV library imports

// None

// BSV additional libs

// none

// ================================================================
// Project imports

import ISA_Decls :: *;

// ================================================================
// INTERFACE

interface CSR_MIP_IFC;
   (* always_ready *)
   method Action reset;

   (* always_ready *)
   method WordXL mv_read;

   (* always_ready, always_enabled *)
   method Action m_external_interrupt_req (Bool req);

   (* always_ready, always_enabled *)
   method Action m_software_interrupt_req (Bool req);

   (* always_ready, always_enabled *)
   method Action m_timer_interrupt_req (Bool req);
endinterface

// ================================================================
// IMPLEMENTATION

(* synthesize *)
module mkCSR_MIP (CSR_MIP_IFC);
   
   Reg #(Bit #(1)) rg_meip <- mkReg (0);
   Reg #(Bit #(1)) rg_mtip <- mkReg (0);
   Reg #(Bit #(1)) rg_msip <- mkReg (0);

   // ----------------------------------------------------------------
   // INTERFACE

   method Action reset;
      rg_meip <= 0; rg_mtip <= 0; rg_msip <= 0;
   endmethod

   method WordXL mv_read;
      Bit #(12) new_mip = {rg_meip, 3'b0, rg_mtip, 3'b0, rg_msip, 3'b0};
      return zeroExtend (new_mip);
   endmethod

   method Action m_external_interrupt_req (Bool req);
      rg_meip <= pack (req);
   endmethod

   method Action m_software_interrupt_req (Bool req);
      rg_msip <= pack (req);
   endmethod

   method Action m_timer_interrupt_req (Bool req);
      rg_mtip <= pack (req);
   endmethod
endmodule

// ================================================================

endpackage
