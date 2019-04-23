From Undecidability.L Require Import Functions.Encoding Datatypes.LOptions Datatypes.LNat.

Instance term_nat_unenc : computable nat_unenc.
Proof.
   extract.
Defined.
