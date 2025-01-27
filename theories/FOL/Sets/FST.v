(* * Finite Set Theory with Adjunction Operation *)
(* ** Axiomatisations *)

Require Export Undecidability.FOL.Utils.FullSyntax.
Require Export Undecidability.FOL.Sets.Signatures.
Import Vector.VectorNotations.
From Stdlib Require Import List.


 
(* ** Signature for ZF axiomatisation, containing function symbols for set operations *)


Import FSTSignature.
Export FSTSignature.

Declare Scope FSTsyn.
Open Scope FSTsyn.

(* ** Axioms *)

Notation "x ∈ y" := (atom _ ZFSignature.ZF_pred_sig elem ([x; y])) (at level 35) : FSTsyn.
Notation "x ≡ y" := (atom (Σ_preds := ZFSignature.ZF_pred_sig) equal ([x; y])) (at level 35) : FSTsyn.

Notation "∅" := (func FST_func_sig eset ([])) : FSTsyn.
Notation "x ::: y" := (func FST_func_sig adj ([x; y])) (at level 31) : FSTsyn.

Definition sub x y :=
  ∀ $0 ∈ x`[↑] → $0 ∈ y`[↑].

Notation "x ⊆ y" := (sub x y) (at level 34) : FSTsyn.

Definition ax_ext :=
  ∀ ∀ $1 ⊆ $0 → $0 ⊆ $1 → $1 ≡ $0.

Definition ax_eset :=
  ∀ ¬ ($0 ∈ ∅).

Definition ax_adj :=
  ∀ ∀ ∀ $0 ∈ $1 ::: $2 ↔ $0 ≡ $1 ∨ $0 ∈ $2.

(* Finite set theory *)

Definition FST :=
  ax_ext :: ax_eset :: ax_adj :: nil.

Definition ax_ind phi :=
  phi[∅..]
   → (∀ ∀ phi[$0 .: (fun n => $(2+n))] → phi[$1 .: (fun n => $(2+n))] → phi[$0 ::: $1 .: (fun n => $(2+n))])
   → ∀ phi.

Inductive FSTI : form -> Prop :=
| FST_base phi : In phi FST -> FSTI phi
| FST_ind phi : FSTI (ax_ind phi).

(* Finite set theory with equalilty axioms *)

Definition ax_refl :=
  ∀ $0 ≡ $0.

Definition ax_sym :=
  ∀ ∀ $1 ≡ $0 → $0 ≡ $1.

Definition ax_trans :=
  ∀ ∀ ∀ $2 ≡ $1 → $1 ≡ $0 → $2 ≡ $0.

Definition ax_eq_elem :=
  ∀ ∀ ∀ ∀ $3 ≡ $1 → $2 ≡ $0 → $3 ∈ $2 → $1 ∈ $0.

Definition FSTeq :=
  ax_refl :: ax_sym :: ax_trans :: ax_eq_elem :: FST.

Inductive FSTIeq : form -> Prop :=
| FSTeq_base phi : In phi FSTeq -> FSTIeq phi
| FSTeq_ind phi : FSTIeq (ax_ind phi).
