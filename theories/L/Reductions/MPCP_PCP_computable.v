From Undecidability.L Require Export Tactics.LTactics Datatypes.LNat Datatypes.LProd Datatypes.Lists.
From Undecidability Require Export PCP.MPCP_PCP PCP.Definitions Problems.PCP.

(* Instance encodable_string : registered (Definitions.string). *)
(* Proof. *)
(*   unfold string, symbol. *)
(*   exact _. *)
(* Defined. *)
(* Hint Extern 0 (L.app (L.app (@enc (Definitions.string) _ _) _) _ >( _ ) _)=> apply list_enc_correct;Lproc : Lrewrite. *)

(* Instance encodable_SRS : registered SRS. *)
(* Proof. *)
(*   unfold SRS, Definitions.stack, Definitions.card, Definitions.string, Definitions.symbol. *)
(*   exact _. *)
(* Defined. *)
(* Hint Extern 0 (L.app (L.app (@enc (SRS) _ _) _) _ >( _ ) _)=> apply list_enc_correct;Lproc : Lrewrite. *)

(* Instance encodable_card : registered (card nat). *)
(* Proof. *)
(*   unfold SRS, Definitions.stack, Definitions.card, Definitions.string, Definitions.symbol. *)
(*   exact _. *)
(* Defined. *)
(* Hint Extern 0 (L.app (@enc (card nat) _ _) _ >( _ ) _)=> apply prod_enc_correct;Lproc : Lrewrite. *)

Hint Transparent Definitions.string SRS card stack: Lrewrite.

Instance computable_fresh : computable fresh.
Proof.
  extract.
Defined.

Instance computable_sym : computable sym.
Proof.
  extract.
Defined.

Instance computable_Sigma : computable Sigma.
Proof.
  extract.
Defined.

Instance computable_dollar : computable dollar.
Proof.
  extract.
Defined.

Instance computable_hash : computable hash.
Proof.
  extract.
Defined.

Instance computable_hash_l : computable hash_l.
Proof.
  extract. 
Defined.

Instance computable_hash_r : computable hash_r.
Proof.
  extract.
Defined.

Instance computable_d : computable d.
Proof.
  extract.
Defined.

Instance computable_e : computable e.
Proof.
  extract.
Defined.

Instance computable_is_cons X `{registered X} : computable (@is_cons X).
Proof.
  extract.
Defined.

Definition both_cons : Definitions.string * Definitions.string -> _ := (fun '(x / y) => is_cons x || is_cons y).

Instance computable_both_cons : computable both_cons.
Proof.
  extract.
Defined.

Definition hash_l_r R x0 y0 := (fun '(x / y) => hash_l R x0 y0 x / hash_r R x0 y0 y).

Instance computable_hash_l_r : computable hash_l_r.
Proof.
  extract.
Defined.

Definition P' := fun (R : SRS) (x0 y0 : Definitions.string) =>
   ([d R x0 y0; e R x0 y0] ++
     map (hash_l_r R x0 y0) 
       (filter both_cons (x0 / y0 :: R)))%list.

Instance computable_P : computable P.
Proof.
  change P with P'. extract.
Defined.

Definition red := (fun '(x, y, R) => P R x y).

Lemma computable_test : computable red.
Proof.
  extract.
Defined.
