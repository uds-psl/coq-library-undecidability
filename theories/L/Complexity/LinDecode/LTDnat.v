From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat.

From Undecidability.L Require Import Functions.Decoding.

From Undecidability.L Require Export LinDecode.LTD_def.

Instance linDec_nat : linTimeDecodable nat.
Proof.
  evar (c:nat). exists c.
  unfold decode,decode_nat;cbn. extract.
  recRel_prettify2;cbn[size];ring_simplify.
  [c]:exact 9.
  all:unfold c;try lia.
Qed.

