// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

package CSR_MSTATUS_Min;

// ================================================================
// CSR (Control and Status Register) Register MSTATUS
// and its restricted views as SSTATUS and USTATUS.

// ================================================================
// BSV library imports

// none

// BSV additional libs

// none

// ================================================================
// Project imports

import ISA_Decls :: *;

// ================================================================
// INTERFACE

// Data structure describing actual bits implemented (needed for CSR writes)
typedef struct {
   Bit #(1) mpie;    // machine previous interrupt enable
   Bit #(1) mie;     // machine interrupt enable
} MSTATUS_Internal deriving (Bits);

interface CSR_MSTATUS_IFC;
   method Action reset;

   method WordXL mv_read;

   // Fixup wordxl and write to reg
   method WordXL mv_write (MSTATUS_Internal mstatus);
   method Action ma_write (MSTATUS_Internal mstatus);

   // Fixup wordxl and write, and return actual value written
   method ActionValue #(WordXL) mav_write (MSTATUS_Internal mstatus);
endinterface

// ================================================================
// IMPLEMENTATION

// TODO: bsc Internal Error in Verilog gen due to parameter being an expression
//       Uncomment next line after bsc fix
// (* synthesize *)
module mkCSR_MSTATUS (CSR_MSTATUS_IFC);
   
   Reg #(Bit #(1)) rg_mpie <- mkReg (0);
   Reg #(Bit #(1)) rg_mie  <- mkReg (0);

   // ----------------------------------------------------------------
   // INTERFACE

   method Action reset;
      rg_mpie <= 0; rg_mie <= 0;
   endmethod

   method WordXL mv_read;
      Bit #(8) new_mstatus = {rg_mpie, 3'b0, rg_mie, 3'b0};
      return (zeroExtend (new_mstatus));
   endmethod

   method WordXL mv_write (MSTATUS_Internal mstatus);
      return zeroExtend (fv_fixup_mstatus (mstatus));
   endmethod

   method Action ma_write (MSTATUS_Internal mstatus);
      rg_mpie <= mstatus.mpie; rg_mie <= mstatus.mie;
   endmethod

   method ActionValue #(WordXL) mav_write (MSTATUS_Internal mstatus);
      rg_mpie <= mstatus.mpie; rg_mie <= mstatus.mie;
      return zeroExtend (fv_fixup_mstatus (mstatus));
   endmethod

endmodule

// ================================================================
// Fix up word to be written to mstatus according to specs for
// supported/ WPRI/ WLRL/ WARL fields.

function Bit #(8) fv_fixup_mstatus (MSTATUS_Internal mstatus);
   // MIE, WPRI_2, SIE, UIE
   Bit #(1) mie    = mstatus.mie;

   // MPIE, WPRI_6, SPIE, UPIE
   Bit #(1) mpie   = mstatus.mpie;

   Bit #(8) fixed_up_val_8 = {mpie, 3'b0, mie, 3'b0};
   return fixed_up_val_8;
endfunction: fv_fixup_mstatus

// ================================================================

endpackage
