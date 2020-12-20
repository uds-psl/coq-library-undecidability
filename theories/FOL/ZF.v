(** * Definition of semantic and deductive ZF-Entailment *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Require Import List.


 
(** ** Signature *)

Existing Instance falsity_on.

Inductive ZF_Funcs : Type :=
| eset : ZF_Funcs
| pair : ZF_Funcs
| union : ZF_Funcs
| power : ZF_Funcs
| om : ZF_Funcs.

Definition ZF_fun_ar (f : ZF_Funcs) : nat :=
  match f with
  | eset => 0
  | pair => 2
  | union => 1
  | power => 1
  | om => 0
  end.

Inductive ZF_Preds : Type :=
| elem : ZF_Preds
| equal : ZF_Preds.

Definition ZF_pred_ar (P : ZF_Preds) : nat :=
  match P with _ => 2 end.

Instance ZF_func_sig : funcs_signature :=
  {| syms := ZF_Funcs; ar_syms := ZF_fun_ar; |}.

Instance ZF_pred_sig : preds_signature :=
  {| preds := ZF_Preds; ar_preds := ZF_pred_ar; |}.



(** ** Axioms *)

Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Notation "x ∈ y" := (atom _ ZF_pred_sig elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 35).
Notation "x ≡ y" := (atom _ ZF_pred_sig equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 35).

Notation "∅" := (func ZF_func_sig eset Vector.nil).
Notation "'ω'" := (func ZF_func_sig om Vector.nil).
Notation "{ x ; y }" := (func ZF_func_sig pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 31).
Notation "⋃ x" := (func ZF_func_sig union (Vector.cons x Vector.nil)) (at level 32).
Notation "'PP' x" := (func ZF_func_sig power (Vector.cons x Vector.nil)) (at level 31).

Notation "x ∪ y" := (⋃ {x; y}) (at level 32).
Notation  "'σ' x" := (x ∪ {x; x}) (at level 32).

Definition sub x y :=
  ∀ $0 ∈ x`[↑] --> $0 ∈ y`[↑].

Notation "x ⊆ y" := (sub x y) (at level 34).

Definition ax_ext :=
  ∀ ∀ $1 ⊆ $0 --> $0 ⊆ $1 --> $1 ≡ $0.

Definition ax_eset :=
  ∀ ¬ ($0 ∈ ∅).

Definition ax_pair :=
  ∀ ∀ ∀ $0 ∈ {$1; $2} <--> $0 ≡ $1 ∨ $0 ≡ $2.

Definition ax_union :=
  ∀ ∀ $0 ∈ ⋃ $1 <--> ∃ $0 ∈ $2 ∧ $1 ∈ $0.

Definition ax_power :=
  ∀ ∀ $0 ∈ PP $1 <--> $0 ⊆ $1.

Definition inductive x :=
  ∅ ∈ x ∧ ∀ $0 ∈ x`[↑] --> σ $0 ∈ x`[↑].

Definition ax_om1 :=
  inductive ω.

Definition ax_om2 :=
  ∀ inductive $0 --> ω ⊆ $0.

Definition ax_sep phi :=
  ∀ ∃ ∀ $0 ∈ $1 <--> $0 ∈ $2 ∧ phi[$0.: Nat.add 3 >> var].

Definition fun_rel phi :=
  ∀ ∀ ∀ phi[$2 .: $1 .: Nat.add 3 >> var] --> phi[$2 .: $0 .: Nat.add 3 >> var] --> $1 ≡ $0.

Definition ax_rep phi :=
  fun_rel phi --> ∀ ∃ ∀ $0 ∈ $1 <--> ∃ $0 ∈ $3 ∧ phi[$0 .: $1 .: Nat.add 4 >> var].

Definition ZF' :=
  ax_ext :: ax_eset :: ax_pair :: ax_union :: ax_power :: ax_om1 :: ax_om2 :: nil.

Inductive ZF : form -> Prop :=
| ZF_base phi : In phi ZF' -> ZF phi
| ZF_sep phi : ZF (ax_sep phi)
| ZF_rep phi : ZF (ax_rep phi).

Definition ax_refl :=
  ∀ $0 ≡ $0.

Definition ax_sym :=
  ∀ ∀ $1 ≡ $0 --> $0 ≡ $1.

Definition ax_trans :=
  ∀ ∀ ∀ $2 ≡ $1 --> $1 ≡ $0 --> $2 ≡ $0.

Definition ax_eq_elem :=
  ∀ ∀ ∀ ∀ $3 ≡ $1 --> $2 ≡ $0 --> $3 ∈ $2 --> $1 ∈ $0.

Definition ZFeq' :=
  ax_refl :: ax_sym :: ax_trans :: ax_eq_elem :: ZF'.

Inductive ZFeq : form -> Prop :=
| ZFeq_base phi : In phi ZFeq' -> ZFeq phi
| ZFeq_sep phi : ZFeq (ax_sep phi)
| ZFeq_rep phi : ZFeq (ax_rep phi).



(** ** Problems *)

Notation extensional M :=
  (forall x y, @i_atom _ _ _ M equal (Vector.cons x (Vector.cons y Vector.nil)) <-> x = y).

(* Semantic entailment restricted to extensional models and core axioms (without sep and rep). *)

Definition entailment_ZF' phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi ZF' -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment restricted to extensional models. *)

Definition entailment_ZF phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, ZF psi -> sigma ⊨ psi) -> rho ⊨ phi.

(* Deductive entailment restricted to intuitionistic rules and core axioms (without sep and rep). *)

Definition deduction_ZF' phi :=
  ZFeq' ⊢I phi.

(* Deductive entailment restricted to intuitionistic rules. *)

Definition deduction_ZF phi :=
  ZFeq ⊢TI phi.


