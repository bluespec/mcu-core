// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

package CSR_MIE_Min;

// ================================================================
// CSR (Control and Status Register) Register MIE

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
   Bit #(1) meie;    // machine external interrupt enable
   Bit #(1) mtie;    // machine timer interrupt enable
   Bit #(1) msie;    // machine software interrupt enable
} MIE_Internal deriving (Bits);

interface CSR_MIE_IFC;
   (* always_ready *)
   method Action reset;

   (* always_ready *)
   method WordXL mv_read;

   // Fixup wordxl and write, and return actual value written
   (* always_ready *)
   method ActionValue #(WordXL) mav_write (MIE_Internal mie);

endinterface

// ================================================================
// IMPLEMENTATION

(* synthesize *)
module mkCSR_MIE (CSR_MIE_IFC);
   
   Reg #(Bit #(1)) rg_meie <- mkReg (0);
   Reg #(Bit #(1)) rg_mtie <- mkReg (0);
   Reg #(Bit #(1)) rg_msie <- mkReg (0);

   // ----------------------------------------------------------------
   // INTERFACE

   method Action reset;
      rg_meie <= 1'b0; rg_mtie <= 1'b0; rg_msie <= 1'b0;
   endmethod

   method WordXL mv_read;
      let mie = MIE_Internal {meie: rg_meie, mtie: rg_mtie, msie: rg_msie};
      return zeroExtend (fv_fixup_mie (mie));
   endmethod

   method ActionValue #(WordXL) mav_write (MIE_Internal mie);
      rg_meie <= mie.meie; rg_mtie <= mie.mtie; rg_msie <= mie.msie;
      let new_mie = fv_fixup_mie (mie);
      return zeroExtend (new_mie);
   endmethod
endmodule

// ================================================================
// Fix up word to be written to mie according to specs for
// supported/ WPRI/ WLRL/ WARL fields.

function Bit #(12) fv_fixup_mie (MIE_Internal  mie);
   // Assemble fixed-up mie
   Bit #(12) new_mie = {mie.meie, 3'b0, mie.mtie, 3'b0, mie.msie, 3'b0};

   return new_mie;
endfunction: fv_fixup_mie

// ================================================================

endpackage
