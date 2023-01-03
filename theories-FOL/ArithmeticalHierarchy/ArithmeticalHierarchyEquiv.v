(* ** Equivalence of Both Definitions *)

From Undecidability.FOL.Syntax Require Import Core.
From Undecidability.FOL.Semantics.Tarski Require Import FullCore.
Require Import Lia Vector Fin List.
Import Vector.VectorNotations.
From Undecidability.FOL.Utils Require Import PrenexNormalForm.
From Undecidability.FOL.ArithmeticalHierarchy Require Import ArithmeticalHierarchySyntactic ArithmeticalHierarchySemantic.

Require Import PeanoNat (* Nat.eqb *) Bool.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.
Derive Signature for vec.

Section ArithmeticalHierarchyEquiv.

  Existing Instance interp_nat.

  Lemma noQuant_dec {ff:falsity_flag} {ϕ}:
    noQuant_ind ϕ -> forall ρ, {(ρ ⊨ ϕ)} + {~(ρ ⊨ ϕ)}.
  Proof.
    intros nQ ρ. induction ϕ  as [| ff P v | ff op φ1 IH1 φ2 IH2|].
    - cbn. now right.
    - destruct P. cbn in *.
      repeat dependent destruction v.
      apply Nat.eq_dec.
    - specialize (IH1 ltac:(now destruct (noQuand_ind_inv nQ))) as [IH1 | IH1];
      specialize (IH2 ltac:(now destruct (noQuand_ind_inv nQ))) as [IH2 | IH2];
      destruct op; cbn.
      all: firstorder.
    - exfalso. inversion nQ.
  Qed.

  Lemma isΣnsyn_in_isΣsem:
    (forall n k (p: vec nat k -> Prop), isΣsyn n p -> isΣsem n p)
 /\ (forall n k (p: vec nat k -> Prop), isΠsyn n p -> isΠsem n p).
  Proof.
    enough (
         (forall (b : falsity_flag) (n : nat) (ϕ : form) (i : isΣf_ind n ϕ) k, isΣsem n ((fun v : vec nat k => vec_to_env v ⊨ ϕ)))
      /\ (forall (b : falsity_flag) (n : nat) (ϕ : form) (i : isΠf_ind n ϕ) k, isΠsem n ((fun v : vec nat k => vec_to_env v ⊨ ϕ)))
     ) as H. {
        split.
        all: intros n k p [ff [ϕ [Σi r]]].
        all: rewrite (PredExt r).
        all: eapply H; eauto.
      }
    apply isΣ_syn_isΠ_syn_mutind.
    - intros ff n ϕ nQ k.
      rewrite PredExt with (g := fun v => (fun v => if (noQuant_dec nQ (vec_to_env v)) then true else false) v = true).
      + apply isΣΠsem0.
      + intros v. now destruct noQuant_dec.
    - intros ff n ϕ iΣ IH k.
      specialize (IH (S k)).
      dependent destruction IH.
      change (isΣsem (S n) (fun v : vec nat k => exists d, (fun v => (vec_to_env v) ⊨ ϕ)(d::v))).
      rewrite H0. now eapply isΣsemTwoEx.
    - intros ff n ϕ iΠ IH k.
      change (isΣsem (S n) (fun v : vec nat k => exists d, (fun v => (vec_to_env v) ⊨ ϕ)(d::v))).
      eapply isΣsemS. now apply IH.
    - intros ff n ϕ nQ k.
      rewrite PredExt with (g := fun v => (fun v => if (noQuant_dec nQ (vec_to_env v)) then true else false) v = true).
      + apply isΣΠsem0.
      + intros v. now destruct noQuant_dec.
    - intros ff n ϕ iΠ IH k.
      specialize (IH (S k)).
      dependent destruction IH.
      change (isΠsem (S n) (fun v : vec nat k => forall d, (fun v => (vec_to_env v) ⊨ ϕ)(d::v))).
      rewrite H0. now apply isΠsemTwoAll.
    - intros ff n ϕ iΣ IH k.
      change (isΠsem (S n) (fun v : vec nat k => forall d, (fun v => (vec_to_env v) ⊨ ϕ)(d::v))).
      eapply isΠsemS. now apply IH.
  Qed.

  (* Rückrichtung annehmen entscheidbar -> Δ1 *)

  Definition decΔ1syn := forall k (f: vec nat k -> bool), isΔsyn 1 (fun v => f v = true).
  Definition decΣ1syn := forall k (f: vec nat k -> bool), isΣsyn 1 (fun v => f v = true).

  Lemma decΣ1syn_decΔ1syn : decΣ1syn <-> decΔ1syn.
  Proof.
    unfold decΣ1syn, decΔ1syn.
    split.
    - intros decΣ1syn k f. split; [apply decΣ1syn|].
      rewrite PredExt with (g := fun v => (fun v => if f v then false else true) v <> true) by (now intros; cbn; destruct f).
      apply Σ1syn_notΠ1_int, decΣ1syn.
    - intros H k f. apply H.
  Qed.

  Lemma decΣ1syn_incl_1 :
    decΣ1syn <->
      (forall k (p : vec nat k -> Prop), isΣsem 1 p -> isΣsyn 1 p)
  /\  (forall k (p : vec nat k -> Prop), isΠsem 1 p -> isΠsyn 1 p).
  Proof.
    split. {
      intros decΔ1syn%decΣ1syn_decΔ1syn.
      split.
      all: intros k p H.
      all: do 2 dependent destruction H.
      all: specialize (decΔ1syn _ f) as [HΣ HΠ].
      - destruct HΣ as [ff [φ [Hφ Hr]]].
        exists ff, (∃φ). split.
        + now constructor 2.
        + intros v. unfold reflecting in Hr. now setoid_rewrite Hr.
      - destruct HΠ as [ff [φ [Hφ Hr]]].
        exists ff, (∀φ). split.
        + now constructor 2.
        + intros v. unfold reflecting in Hr. now setoid_rewrite Hr.
    } {
      intros H k f. apply H. apply isΣΠsem0.
    }
  Qed.
  
  Lemma isΣsem_in_isΣsyn :
  decΣ1syn ->
    (forall n k (p: vec nat k -> Prop), isΣsem n p -> n <> 0 -> isΣsyn n p)
  /\ (forall n k (p: vec nat k -> Prop), isΠsem n p -> n <> 0 -> isΠsyn n p).
  Proof.
    intros HdecΔ1%decΣ1syn_incl_1.
    apply isΣsem_isΠsem_mutind; try lia.
    - intros [] k p H IH eq. { apply HdecΔ1. now apply isΣsemS. }
      destruct (IH ltac:(lia)) as [ff [ϕ [IH1 IH2]]].
      exists ff, (∃ ϕ). split.
      + now apply isΠex.
      + revert IH2. clear. firstorder.
    - intros [] k p H IH eq. { apply HdecΔ1. now apply isΠsemS. }
      destruct (IH ltac:(lia)) as [ff [ϕ [IH1 IH2]]].
      exists ff, (∀ ϕ). split.
      + now apply isΣall.
      + revert IH2. clear. firstorder.
  Qed.

End ArithmeticalHierarchyEquiv.
