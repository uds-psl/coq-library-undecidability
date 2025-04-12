(* * ZF set theory without Skolem function symbols *)
(* ** Axiomatisations using membership and equality *)

Require Export Undecidability.FOL.Utils.FullSyntax.
Require Export Undecidability.FOL.Sets.Signatures.
Require Export Undecidability.FOL.Sets.ZF.
Import Vector.VectorNotations.
From Stdlib Require Import List.


Declare Scope minZFsyn.
Open Scope minZFsyn.
 
(* ** Minimal signature only containing membership and equality, no function symbols *)

Import BinSig.
Import ZFSignature.
Export BinSig.
Export ZFSignature.

#[global]
Existing Instance ZF_pred_sig | 0.

#[global]
Existing Instance sig_empty | 0.

Notation "x ∈' y" := (atom sig_empty ZF_pred_sig elem ([x; y])) (at level 35) : minZFsyn.
Notation "x ≡' y" := (atom sig_empty ZF_pred_sig equal ([x; y])) (at level 35) : minZFsyn.



(* ** Characterisations of set operations *)

Fixpoint shift `{funcs_signature} `{preds_signature} n (t : term) :=
  match n with 
  | O => t
  | S n => subst_term ↑ (shift n t)
  end.

Definition is_eset (t : term) :=
  ∀ ¬ ($0 ∈ t`[↑]).

Definition is_pair (x y t : term) :=
  ∀ $0 ∈ t`[↑] ↔ $0 ≡ x`[↑] ∨ $0 ≡ y`[↑].

Definition is_union (x t : term) :=
  ∀ $0 ∈ t`[↑] ↔ ∃ $0 ∈ shift 2 x ∧ $1 ∈ $0.

Definition sub' (x y : term) :=
  ∀ $0 ∈ x`[↑] → $0 ∈ y`[↑].

Definition is_power (x t : term) :=
  ∀ $0 ∈ t`[↑] ↔ sub' $0 x`[↑].

Definition is_sigma (x t : term) :=
  ∀ $0 ∈ t`[↑] ↔ $0 ∈ x`[↑] ∨ $0 ≡ x`[↑].

Definition is_inductive (t : term) :=
  (∃ is_eset $0 ∧ $0 ∈ t`[↑]) ∧ ∀ $0 ∈ t`[↑] → (∃ is_sigma $1 $0 ∧ $0 ∈ shift 2 t).

Definition is_om (t : term) :=
  is_inductive t ∧ ∀ is_inductive $0 → sub' t`[↑] $0.



(* ** Symbol-free axiomatisation *)

Definition ax_ext' :=
  ∀ ∀ sub' $1 $0 → sub' $0 $1 → $1 ≡' $0.

Definition ax_eset' :=
  ∃ is_eset $0.

Definition ax_pair' :=
  ∀ ∀ ∃ is_pair $2 $1 $0.

Definition ax_union' :=
  ∀ ∃ is_union $1 $0.

Definition ax_power' :=
  ∀ ∃ is_power $1 $0.

Definition ax_om' :=
  ∃ is_om $0.

Definition ax_refl' :=
  ∀ $0 ≡' $0.

Definition ax_sym' :=
  ∀ ∀ $1 ≡' $0 → $0 ≡' $1.

Definition ax_trans' :=
  ∀ ∀ ∀ $2 ≡' $1 → $1 ≡' $0 → $2 ≡' $0.

Definition ax_eq_elem' :=
  ∀ ∀ ∀ ∀ $3 ≡' $1 → $2 ≡' $0 → $3 ∈' $2 → $1 ∈' $0.

(* List of core axioms without schemes for separation and replacement *)

Definition minZF' :=
  ax_ext' :: ax_eset' :: ax_pair' :: ax_union' :: ax_power' :: ax_om' :: nil.

(* List of core axioms plus equality axioms *)

Definition minZFeq' :=
  ax_refl' :: ax_sym' :: ax_trans' :: ax_eq_elem' :: minZF'.

Definition ax_sep' phi :=
  ∀ ∃ ∀ $0 ∈' $1 ↔ $0 ∈' $2 ∧ phi[$0.: Nat.add 3 >> var].

Definition fun_rel' phi :=
  ∀ ∀ ∀ phi[$2 .: $1 .: Nat.add 3 >> var] → phi[$2 .: $0 .: Nat.add 3 >> var] → $1 ≡' $0.

Definition ax_rep' phi :=
  fun_rel' phi → ∀ ∃ ∀ $0 ∈' $1 ↔ ∃ $0 ∈' $3 ∧ phi[$0 .: $1 .: Nat.add 4 >> var].

(* Theory of Z including the separation and replacement schemes *)

Inductive minZ : form -> Prop :=
| minZ_base phi : In phi minZF' -> minZ phi
| minZ_sep phi : minZ (ax_sep' phi).

(* Theory of Z plus equality axioms *)

Inductive minZeq : form -> Prop :=
| minZeq_base phi : In phi minZFeq' -> minZeq phi
| minZeq_sep phi : minZeq (ax_sep' phi).

(* Theory of full ZF including the separation and replacement schemes *)

Inductive minZF : form -> Prop :=
| minZF_base phi : In phi minZF' -> minZF phi
| minZF_sep phi : minZF (ax_sep' phi)
| minZF_rep phi : minZF (ax_rep' phi).

(* Theory of full ZF plus equality axioms *)

Inductive minZFeq : form -> Prop :=
| minZFeq_base phi : In phi minZFeq' -> minZFeq phi
| minZFeq_sep phi : minZFeq (ax_sep' phi)
| minZFeq_rep phi : minZFeq (ax_rep' phi).

