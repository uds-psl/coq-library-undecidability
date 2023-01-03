(* * ZF set theory with Skolem function symbols *)
(* ** Axiomatisations *)

Require Export Undecidability.FOL.FullSyntax.
Require Export Undecidability.FOL.Sets.Signatures.
Import Vector.VectorNotations.
Require Import List.

Declare Scope syn.
Open Scope syn.

(* ** Signature for ZF axiomatisation, containing function symbols for set operations *)

Import ZFSignature.
Export ZFSignature.


(* ** Axioms *)

Notation "x ∈ y" := (atom _ ZF_pred_sig elem ([x; y])) (at level 35) : syn.
Notation "x ≡ y" := (atom (Σ_preds := ZF_pred_sig) equal ([x; y])) (at level 35) : syn.

Notation "∅" := (func ZF_func_sig eset ([])) : syn.
Notation "'ω'" := (func ZF_func_sig om ([])) : syn.
Notation "{ x ; y }" := (func ZF_func_sig pair ([x; y])) (at level 31) : syn.
Notation "⋃ x" := (func ZF_func_sig union ([x])) (at level 32) : syn.
Notation "'PP' x" := (func ZF_func_sig power ([x])) (at level 31) : syn.
Notation "x ∪ y" := (⋃ {x; y}) (at level 32) : syn.
Notation  "'σ' x" := (x ∪ {x; x}) (at level 32) : syn.

Definition sub x y :=
  ∀ $0 ∈ x`[↑] → $0 ∈ y`[↑].

Notation "x ⊆ y" := (sub x y) (at level 34) : syn.

Definition ax_ext :=
  ∀ ∀ $1 ⊆ $0 → $0 ⊆ $1 → $1 ≡ $0.

Definition ax_eset :=
  ∀ ¬ ($0 ∈ ∅).

Definition ax_pair :=
  ∀ ∀ ∀ $0 ∈ {$1; $2} ↔ $0 ≡ $1 ∨ $0 ≡ $2.

Definition ax_union :=
  ∀ ∀ $0 ∈ ⋃ $1 ↔ ∃ $0 ∈ $2 ∧ $1 ∈ $0.

Definition ax_power :=
  ∀ ∀ $0 ∈ PP $1 ↔ $0 ⊆ $1.

Definition inductive x :=
  ∅ ∈ x ∧ ∀ $0 ∈ x`[↑] → σ $0 ∈ x`[↑].

Definition ax_om1 :=
  inductive ω.

Definition ax_om2 :=
  ∀ inductive $0 → ω ⊆ $0.

Definition ax_sep phi :=
  ∀ ∃ ∀ $0 ∈ $1 ↔ $0 ∈ $2 ∧ phi[$0.: Nat.add 3 >> var].

Definition fun_rel phi :=
  ∀ ∀ ∀ phi[$2 .: $1 .: Nat.add 3 >> var] → phi[$2 .: $0 .: Nat.add 3 >> var] → $1 ≡ $0.

Definition ax_rep phi :=
  fun_rel phi → ∀ ∃ ∀ $0 ∈ $1 ↔ ∃ $0 ∈ $3 ∧ phi[$0 .: $1 .: Nat.add 4 >> var].

(* Hereditarily finite set theory *)

Definition HF :=
  ax_ext :: ax_eset :: ax_pair :: ax_union :: ax_power :: nil.

Definition ax_no_inductive :=
  ∀ ¬ inductive $0.

Definition HFN :=
  ax_no_inductive :: HF.

(* List of core axioms without schemes for separation and replacement *)

Definition ZF' :=
  ax_ext :: ax_eset :: ax_pair :: ax_union :: ax_power :: ax_om1 :: ax_om2 :: nil.

(* Theory of Z including the separation scheme *)

Inductive Z : form -> Prop :=
| Z_base phi : In phi ZF' -> Z phi
| Z_sep phi : Z (ax_sep phi).

(* Theory of full ZF including the separation and replacement schemes *)

Inductive ZF : form -> Prop :=
| ZF_base phi : In phi ZF' -> ZF phi
| ZF_sep phi : ZF (ax_sep phi)
| ZF_rep phi : ZF (ax_rep phi).

Definition ax_refl :=
  ∀ $0 ≡ $0.

Definition ax_sym :=
  ∀ ∀ $1 ≡ $0 → $0 ≡ $1.

Definition ax_trans :=
  ∀ ∀ ∀ $2 ≡ $1 → $1 ≡ $0 → $2 ≡ $0.

Definition ax_eq_elem :=
  ∀ ∀ ∀ ∀ $3 ≡ $1 → $2 ≡ $0 → $3 ∈ $2 → $1 ∈ $0.

(* List of HF axioms plus equality axioms *)

Definition HFeq :=
  ax_refl :: ax_sym :: ax_trans :: ax_eq_elem :: HF.

Definition HFNeq :=
  ax_refl :: ax_sym :: ax_trans :: ax_eq_elem :: HFN.

(* List of core axioms plus equality axioms *)

Definition ZFeq' :=
  ax_refl :: ax_sym :: ax_trans :: ax_eq_elem :: ZF'.

(* Theory of Z plus equality axioms *)

Inductive Zeq : form -> Prop :=
| Zeq_base phi : In phi ZFeq' -> Zeq phi
| Zeq_sep phi : Zeq (ax_sep phi).

(* Theory of full ZF plus equality axioms *)

Inductive ZFeq : form -> Prop :=
| ZFeq_base phi : In phi ZFeq' -> ZFeq phi
| ZFeq_sep phi : ZFeq (ax_sep phi)
| ZFeq_rep phi : ZFeq (ax_rep phi).



(* ** Problems *)

Notation extensional M :=
  (forall x y, @i_atom _ ZF_pred_sig _ M equal ([x; y]) <-> x = y).

(* Semantic entailment restricted to core axioms (without sep and rep) with equality axioms. *)

Definition entailment_ZFeq' phi :=
  forall D (M : interp D) (rho : nat -> D), (forall sigma psi, In psi ZFeq' -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment restricted to extensional models and hereditarily finite sets. *)

Definition entailment_HF phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi HF -> sigma ⊨ psi) -> rho ⊨ phi.

Definition entailment_HFN phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi HFN -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment restricted to extensional models and core axioms (without sep and rep). *)

Definition entailment_ZF' phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi ZF' -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment for Z restricted to extensional models. *)

Definition entailment_Z phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, Z psi -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment for ZF restricted to extensional models. *)

Definition entailment_ZF phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, ZF psi -> sigma ⊨ psi) -> rho ⊨ phi.

(* Deductive entailment restricted to hereditarily finite sets. *)

Definition deduction_HF phi :=
  HFeq ⊢I phi.

Definition deduction_HFN phi :=
  HFNeq ⊢I phi.

(* Deductive entailment restricted to intuitionistic rules and core axioms (without sep and rep). *)

Definition deduction_ZF' phi :=
  ZFeq' ⊢I phi.

(* Deductive entailment for Z restricted to intuitionistic rules. *)

Definition deduction_Z phi :=
  Zeq ⊢TI phi.

(* Deductive entailment for ZF restricted to intuitionistic rules. *)

Definition deduction_ZF phi :=
  ZFeq ⊢TI phi.


