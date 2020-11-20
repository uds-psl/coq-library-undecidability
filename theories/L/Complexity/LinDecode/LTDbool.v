From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LBool.

From Undecidability.L Require Import Functions.Decoding.

From Undecidability.L Require Export LinDecode.LTD_def.

Instance linDec_bool : linTimeDecodable bool.
Proof.
  evar (c : nat). exists c. unfold decode, decode_bool. extract. 
  solverec. [c]: exact 5. all: subst c; lia.
Qed. 
