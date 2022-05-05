package Shifter_IFC;

import ClientServer :: *;
import GetPut :: *;
import ISA_Decls  :: *;

// ================================================================
// SBox interface

interface Shifter_Box_IFC;
   interface Server #(Token, Token) server_reset;

   // request
   // 'right' specifies right or left shift
   // 'v1' is the operand to be shifted
   // 'v2' has the shift amount ([4:0] for RV32, [5:0] for RV64)
   //      and whether right-shifts are logical ([5]=0) or arithmetic ([5]=1)
   (* always_ready *)
   method Action  req (Bool right, Word v1, Word v2);

   // response
   (* always_ready *)   method Bool  valid;
   (* always_ready *)   method Word  word;
endinterface

endpackage
