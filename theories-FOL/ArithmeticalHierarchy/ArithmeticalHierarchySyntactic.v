(* * Arithmetical Hierarchy *)
(* ** Arithmetical Hierarchy in First-Order Arithmetic *)

From FOL Require Import FullSyntax.
Require Import Lia Vector Fin List.
Import Vector.VectorNotations.
From FOL.Utils Require Import PrenexNormalForm.
Require Import Eqdep_dec.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Require Import PeanoNat (* Nat.eqb *) Bool.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.

Section ArithmeticalHierarchySyntactic.
    Definition interp_nat : interp nat.
    Proof.
    split.
    - destruct f; intros v.
        + exact 0.
        + exact (S (Vector.hd v) ).
        + exact (Vector.hd v + Vector.hd (Vector.tl v) ).
        + exact (Vector.hd v * Vector.hd (Vector.tl v) ).
    - destruct P. intros v.
        exact (Vector.hd v = Vector.hd (Vector.tl v) ).
    Defined.
    Existing Instance interp_nat.

    Definition equiv_form {b: falsity_flag} (ϕ1 ϕ2: form b) := forall ρ, sat ρ ϕ1 <-> sat ρ ϕ2.

    Notation "φ1 ≡ φ2" := (equiv_form φ1 φ2) (at level 70).

    Inductive isΣf_ind : forall b (n: nat), form b -> Prop :=
    | isΣnoQuant {b} n (f: form b) : noQuant_ind f -> isΣf_ind n f
    | isΣex {b} n (f: form b) : isΣf_ind (S n) f -> isΣf_ind (S n) (∃ f)
    | isΠex {b} n (f: form b) : isΠf_ind n f -> isΣf_ind (S n) (∃ f)

    with isΠf_ind : forall b (n: nat), form b -> Prop :=
    | isΠnoQuant {b} n (f: form b) : noQuant_ind f -> isΠf_ind n f
    | isΠall {b} n (f: form b) : isΠf_ind (S n) f -> isΠf_ind (S n) (∀ f)
    | isΣall {b} n (f: form b) : isΣf_ind n f -> isΠf_ind (S n) (∀ f).

    Definition isΔf_ind {b} (n: nat) (f: form b) : Prop := isΣf_ind n f /\ isΠf_ind n f.

    Derive Signature for isΣf_ind.
    Derive Signature for isΠf_ind.
    #[local] Hint Constructors isΣf_ind : core.
    #[local] Hint Constructors isΠf_ind : core.

    (* generacte induction scheme *)
    Scheme isΣf_ind_isΠf_ind_ind := Induction for isΣf_ind Sort Prop
    with isΠf_ind_isΣf_ind_ind := Induction for isΠf_ind Sort Prop.
    (* https://coq.inria.fr/refman/proofs/writing-proofs/reasoning-inductives.html#combined-scheme *)
    Combined Scheme isΣ_syn_isΠ_syn_mutind from isΣf_ind_isΠf_ind_ind,isΠf_ind_isΣf_ind_ind.

    Definition isΣform {b} (n: nat) (f: form b) : Prop := exists f', f ≡ f' /\ isΣf_ind n f'.
    Definition isΠform {b} (n: nat) (f: form b) : Prop := exists f', f ≡ f' /\ isΠf_ind n f'.
    Definition isΔform {b} (n: nat) (f: form b) : Prop := isΣform n f /\ isΠform n f.

    Fixpoint vec_to_env {k} (v : vec nat k) (n : nat) :=
    match v with
    | Vector.nil _ => 42
    | Vector.cons _ x _ v' => 
        match n with
        | 0 => x
        | S n => vec_to_env v' n
        end
    end.

    Definition reflecting {k} (p : vec nat k -> Prop) {ff: falsity_flag} (ϕ : form ff) := 
    forall v, p v <-> (vec_to_env v) ⊨ ϕ.
    
    Definition isΣsyn n {k} (p: vec nat k -> Prop) := exists (ff: falsity_flag) ϕ, isΣf_ind n ϕ /\ reflecting p ϕ.
    Definition isΠsyn n {k} (p: vec nat k -> Prop) := exists (ff: falsity_flag) ϕ, isΠf_ind n ϕ /\ reflecting p ϕ.
    Definition isΔsyn n {k} (p: vec nat k -> Prop) := isΣsyn n p /\ isΠsyn n p.

    Lemma extensional_Σsyn {k} (p q : vec nat k -> Prop) :
      (forall v, p v <-> q v) -> forall n, isΣsyn n q -> isΣsyn n p.
    Proof.
      intros eq n [φ Hφ].
      exists φ. firstorder.
    Qed.

    Lemma extensional_Πsyn {k} (p q : vec nat k -> Prop) :
      (forall v, p v <-> q v) -> forall n, isΠsyn n q -> isΠsyn n p.
    Proof.
      intros eq n [φ Hφ].
      exists φ. firstorder.
    Qed.

    Lemma reflecting_neq {k} {p : vec nat k -> Prop} {ff: falsity_flag} {ϕ : form ff} :
      reflecting p ϕ -> (forall v, ~p v <-> ~(vec_to_env v) ⊨ ϕ).
    Proof. firstorder. Qed.

    Lemma PNF_isΣorΠ_syn {ff: falsity_flag} f (pnf : PNF_ind f):
    { n & sum (isΣf_ind n f) (isΠf_ind n f) }.
    Proof.
    (* PNF_ind_rec is an eliminator to Type and enables strong induction *)
    induction pnf as [b ϕ H|b [] ϕ H [n [IH|IH]]].
    - exists 0. left. now eapply isΣnoQuant.
    - exists (S n). right. now eapply isΣall.
    - destruct n.
        + exists 1. right. inversion IH. eapply isΣall.
        apply inj_pair2_eq_dec in H0.
        * subst. now constructor.
        * decide equality.
        + exists (S n). right. now eapply isΠall.
    - destruct n.
        + exists 1. left. inversion IH. eapply isΠex.
        apply inj_pair2_eq_dec in H0.
        * subst. now constructor.
        * decide equality.
        + exists (S n). left. now eapply isΣex.
    - exists (S n). left. now eapply isΠex.
    Defined.

    (* Compute (projT1 (PNF_isΣorΠ_syn (convert_PNF_PNF (∀∃∀∃∀ ⊥)))). *)
    (* Compute (projT2 (PNF_isΣorΠ_syn (convert_PNF_PNF (∀∃∀∃∀ ⊥)))). *)

    Lemma isΣΠf_PNF:
    (forall (b : falsity_flag) n f, isΣf_ind n f -> PNF_ind f)
    /\ (forall (b : falsity_flag) n f, isΠf_ind n f -> PNF_ind f).
    Proof.
    apply isΣ_syn_isΠ_syn_mutind; now constructor.
    Qed.

    Lemma isΣΠf_iff_PNF {ff: falsity_flag} φ:
    PNF_ind φ <-> exists n, isΣf_ind n φ \/ isΠf_ind n φ.
    Proof.
    split.
    - intros pnf. destruct (PNF_isΣorΠ_syn pnf) as [n [|]]; eauto.
    - now intros [n [?%isΣΠf_PNF|?%isΣΠf_PNF]].
    Qed.

    Lemma inclusionΣinΣ1andΠinΠi_syn:
    (forall (b : falsity_flag) n f, isΣf_ind n f -> isΣf_ind (S n) f)
    /\ (forall (b : falsity_flag) n f, isΠf_ind n f -> isΠf_ind (S n) f).
    Proof.
    apply isΣ_syn_isΠ_syn_mutind; eauto.
    Qed.

    Lemma isΣinΣ1 {b : falsity_flag} n f:
    isΣform n f -> isΣform (S n) f.
    Proof.
    unfold isΣform. intros [? []]. eexists. split; eauto. apply inclusionΣinΣ1andΠinΠi_syn. eauto.
    Qed.

    Lemma isΠinΠ1 {b : falsity_flag} n f:
    isΠform n f -> isΠform (S n) f.
    Proof.
    unfold isΠform. intros [? []]. eexists. split; eauto. apply inclusionΣinΣ1andΠinΠi_syn. eauto.
    Qed.

    Lemma isΣinΣpLsyn {k} (p: vec nat k -> Prop) n l :
    isΣsyn n p -> isΣsyn (l + n) p.
    Proof.
    unfold isΣsyn. intros [ff [ϕ [i r]]]. exists ff, ϕ. split; [| assumption].
    induction l as [| l IH].
    - exact i.
    - cbn. now apply inclusionΣinΣ1andΠinΠi_syn.
    Qed.

    Lemma isΠinΠpLsyn {k} (p: vec nat k -> Prop) n l :
    isΠsyn n p -> isΠsyn (l + n) p.
    Proof.
    unfold isΠsyn. intros [ff [ϕ [i r]]]. exists ff, ϕ. split; [| assumption].
    induction l as [| l IH].
    - exact i.
    - cbn. now apply inclusionΣinΣ1andΠinΠi_syn.
    Qed.

    Fixpoint turnFalsityOn {ff} (ϕ : form ff) : form falsity_on :=
        match ϕ with
        | ⊥ => ⊥
        | atom P t => atom P t
        | bin _ _ _ _ op ϕ1 ϕ2 => bin op (turnFalsityOn ϕ1) (turnFalsityOn ϕ2)
        | quant _ _ _ _ q ϕ => quant q (turnFalsityOn ϕ)
        end.
      
      Lemma turnFalsityOn_eqiv {ff} (ϕ: form ff) :
        forall ρ, ρ ⊨ ϕ <-> ρ ⊨ (turnFalsityOn ϕ).
      Proof.
        induction ϕ as [| | ? op φ1 IH1 φ2 IH2 | ? op φ IH ]; intros ρ; cbn; try reflexivity.
        all: destruct op; try now rewrite IH1, IH2.
        all: now setoid_rewrite IH.
      Qed.
    
      Lemma turnFalsityOn_noQuant {ff} {ϕ: form ff} :
        noQuant_ind ϕ <-> noQuant_ind (turnFalsityOn ϕ).
      Proof.
        induction ϕ as [| | ? op φ1 IH1 φ2 IH2 | ? op φ IH ]; cbn; try reflexivity.
        - split; inversion 1; now constructor.
        - split; intros H%noQuand_ind_inv; cbn in H; constructor;
          [rewrite <- IH1 | rewrite <- IH2 | rewrite IH1 | rewrite IH2]; apply H.
        - split; intros []%noQuand_ind_inv.
      Qed.
      
      Lemma turnFalsityOn_isΣΠf_ind :
         (forall (b : falsity_flag) (n : nat) (ϕ : form) (i : isΣf_ind n ϕ), isΣf_ind n (turnFalsityOn ϕ))
      /\ (forall (b : falsity_flag) (n : nat) (ϕ : form) (i : isΠf_ind n ϕ), isΠf_ind n (turnFalsityOn ϕ)).
      Proof.
        apply isΣ_syn_isΠ_syn_mutind.
        - intros ff n ϕ. intros H%turnFalsityOn_noQuant. now constructor.
        - intros ff n f H IH. now apply isΣex.
        - intros ff n f H IH. now apply isΠex.
        - intros ff n ϕ. intros H%turnFalsityOn_noQuant. now constructor.
        - intros ff n f H IH. now apply isΠall.
        - intros ff n f H IH. now apply isΣall.
      Qed.
    
      Lemma Σ1syn_notΠ1_int k (p: vec nat k -> Prop) :
        isΣsyn 1 p -> isΠsyn 1 (fun v => ~(p v)).
      Proof.
        intros [ff [ϕ [iΣ eq]]].
        eapply (extensional_Πsyn (reflecting_neq eq)).
        unfold reflecting in eq.
        enough (isΠsyn 1 (fun v : vec nat k => ~ vec_to_env v ⊨ ϕ)) as [ψ Hψ] by (exists ψ; firstorder).
        clear eq p.
        apply isΣΠf_PNF in iΣ as PNF. revert k. induction PNF; intros k.
        - exists falsity_on. exists (¬(turnFalsityOn ϕ)). split.
          + apply isΠnoQuant. apply turnFalsityOn_noQuant in H. now repeat constructor.
          + intros v. cbn. rewrite turnFalsityOn_eqiv. tauto.
        - destruct op.
          + dependent destruction iΣ.
            * inversion H.
            * inversion H.
            * inversion H0.
          + dependent destruction iΣ.
            * inversion H.
            * injection H. intros <-%Eqdep.EqdepTheory.inj_pair2.
              specialize (IHPNF iΣ (S k)) as [ff [ψ [iΠ r]]].
              exists ff. exists (∀ ψ). split; [now constructor|].
              intros v. cbn. split.
              -- intros nE x. assert ((x .: vec_to_env v) = vec_to_env (x :: v)) as eq by reflexivity. rewrite eq.
                apply r. rewrite <- eq. intros sϕ. apply nE. now exists x.
              -- intros A [x E]. specialize (A x). replace (x .: vec_to_env v) with (vec_to_env (x :: v)) in * by reflexivity.
                now apply r in A.
            * injection H0. intros <-%Eqdep.EqdepTheory.inj_pair2.
              exists falsity_on, (∀ ¬ turnFalsityOn ϕ). split. { apply isΠall, isΠnoQuant. repeat constructor. rewrite <- turnFalsityOn_noQuant. now dependent destruction H. }
              intros v. cbn. split.
              -- intros nE x sϕ. apply nE. exists x. now apply turnFalsityOn_eqiv.
              -- intros A [x E]. specialize (A x). now apply turnFalsityOn_eqiv in E.
      Qed.

  Definition DN := forall p, ~~p -> p.
  
  Lemma negΣinΠsyn:
    DN ->
     (forall n k (p: vec nat k -> Prop), isΣsyn n p -> isΠsyn n (fun v => ~(p v)))
  /\ (forall n k (p: vec nat k -> Prop), isΠsyn n p -> isΣsyn n (fun v => ~(p v))).
  Proof.
    intros DN.
    enough (
         (forall (b : falsity_flag) (n : nat) (ϕ : form) (i : isΣf_ind n ϕ) k (p: vec nat k -> Prop), reflecting p ϕ -> isΠsyn n (fun v => ~(p v)))
      /\ (forall (b : falsity_flag) (n : nat) (ϕ : form) (i : isΠf_ind n ϕ) k (p: vec nat k -> Prop), reflecting p ϕ -> isΣsyn n (fun v => ~(p v)))
     ) as H. {
        split.
        all: intros n k p [ϕ [Σi r]].
        all: eapply H; apply r.
      }
    apply isΣ_syn_isΠ_syn_mutind.
    - intros ff n ϕ nQ k p r.
      exists falsity_on, (¬(turnFalsityOn ϕ)). split.
      + constructor. constructor. { now rewrite <- turnFalsityOn_noQuant. } { constructor. }
      + unfold reflecting in *. intros v. specialize (r v). rewrite turnFalsityOn_eqiv in r. cbn. tauto.
    - intros ff n ϕ _ IH k p r. apply (extensional_Πsyn (reflecting_neq r)).
      specialize (IH (S k) (fun v => vec_to_env v ⊨ ϕ) ltac:(now unfold reflecting)) as [ffφ [φ [IH IH']]].
      exists ffφ, (∀ φ). split.
      + apply isΠall, IH.
      + unfold reflecting in *. intros v. assert ((~ vec_to_env v ⊨ (∃ ϕ)) <-> vec_to_env v ⊨ (¬(turnFalsityOn (∃ ϕ)))) as ->. {
        rewrite turnFalsityOn_eqiv. cbn. tauto.
      } cbn [turnFalsityOn]. rewrite (equivToCoq (PNF_notExists _ _)). cbn. split.
        * intros H d. assert ((d .: vec_to_env v) = vec_to_env (d::v)) as eq by reflexivity. rewrite eq. apply IH'. rewrite <- eq.
          intros H'%turnFalsityOn_eqiv. now apply (H d).
        * intros H d. assert ((d .: vec_to_env v) = vec_to_env (d::v)) as eq by reflexivity.
          rewrite eq. specialize (H d). rewrite eq in H. intros H'. specialize (IH' (d::v)). apply IH'. { apply H. }
          now apply turnFalsityOn_eqiv.
    - intros ff n ϕ _ IH k p r. apply (extensional_Πsyn (reflecting_neq r)).
      specialize (IH (S k) (fun v => vec_to_env v ⊨ ϕ) ltac:(now unfold reflecting)) as [ffφ [φ [IH IH']]].
      exists ffφ, (∀ φ). split.
      + apply isΣall, IH.
      + unfold reflecting in *. intros v. assert ((~ vec_to_env v ⊨ (∃ ϕ)) <-> vec_to_env v ⊨ (¬(turnFalsityOn (∃ ϕ)))) as ->. {
        rewrite turnFalsityOn_eqiv. cbn. tauto.
      } cbn [turnFalsityOn]. rewrite (equivToCoq (PNF_notExists _ _)). cbn. split.
        * intros H d. assert ((d .: vec_to_env v) = vec_to_env (d::v)) as eq by reflexivity. rewrite eq. apply IH'. rewrite <- eq.
          intros H'%turnFalsityOn_eqiv. now apply (H d).
        * intros H d. assert ((d .: vec_to_env v) = vec_to_env (d::v)) as eq by reflexivity. rewrite eq.
          specialize (H d). rewrite eq in H. intros H'. specialize (IH' (d::v)). apply IH'. { apply H. }
          now apply turnFalsityOn_eqiv.
    - intros ff n ϕ nQ k p r.
      exists falsity_on, (¬(turnFalsityOn ϕ)). split.
      + constructor. constructor. { now rewrite <- turnFalsityOn_noQuant. } { constructor. }
      + unfold reflecting in *. intros v. specialize (r v). rewrite turnFalsityOn_eqiv in r. cbn. tauto.
    - intros ff n ϕ _ IH k p r. apply (extensional_Σsyn (reflecting_neq r)).
      specialize (IH (S k) (fun v => vec_to_env v ⊨ ϕ) ltac:(now unfold reflecting)) as [ffφ [φ [IH IH']]].
      exists ffφ, (∃ φ). split.
      + apply isΣex, IH.
      + unfold reflecting in *. intros v. assert ((~ vec_to_env v ⊨ (∀ ϕ)) <-> vec_to_env v ⊨ (¬(turnFalsityOn (∀ ϕ)))) as ->. {
        rewrite turnFalsityOn_eqiv. cbn. tauto.
      } cbn [turnFalsityOn]. rewrite (PNF_notAll DN). cbn. split.
        * intros [d H]. exists d. assert ((d .: vec_to_env v) = vec_to_env (d::v)) as eq by reflexivity. rewrite eq in *. apply IH'. rewrite <- eq.
          intros H'%turnFalsityOn_eqiv. now apply H.
        * intros [d H]. exists d. assert ((d .: vec_to_env v) = vec_to_env (d::v)) as eq by reflexivity. rewrite eq in *.
          intros H'. specialize (IH' (d::v)). apply IH'. { apply H. }
          now apply turnFalsityOn_eqiv.
    - intros ff n ϕ _ IH k p r. apply (extensional_Σsyn (reflecting_neq r)).
      specialize (IH (S k) (fun v => vec_to_env v ⊨ ϕ) ltac:(now unfold reflecting)) as [ffφ [φ [IH IH']]].
      exists ffφ, (∃ φ). split.
      + apply isΠex, IH.
      + unfold reflecting in *. intros v. assert ((~ vec_to_env v ⊨ (∀ ϕ)) <-> vec_to_env v ⊨ (¬(turnFalsityOn (∀ ϕ)))) as ->. {
        rewrite turnFalsityOn_eqiv. cbn. tauto.
      } cbn [turnFalsityOn]. rewrite (PNF_notAll DN). cbn. split.
        * intros [d H]. exists d. assert ((d .: vec_to_env v) = vec_to_env (d::v)) as eq by reflexivity. rewrite eq in *. apply IH'. rewrite <- eq.
          intros H'%turnFalsityOn_eqiv. now apply H.
        * intros [d H]. exists d. assert ((d .: vec_to_env v) = vec_to_env (d::v)) as eq by reflexivity. rewrite eq in *.
          intros H'. specialize (IH' (d::v)). apply IH'. { apply H. }
          now apply turnFalsityOn_eqiv.
  Qed.

End ArithmeticalHierarchySyntactic.
