From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import Lists LTerm.

From Undecidability.L Require Import Functions.Decoding.

From Undecidability.L Require Export LinDecode.LTD_def.

Global Instance linDec_list X `{_:linTimeDecodable X}: linTimeDecodable (list X).
Proof.
  evar (c:nat). exists c.
  unfold decode,decode_list,list_decode;cbn.
  extract.
  recRel_prettify2;cbn[size];ring_simplify.
  [c]:exact (max (c__linDec X) 12).
  all:unfold c;try nia.
Qed.
