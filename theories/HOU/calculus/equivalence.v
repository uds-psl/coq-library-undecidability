Set Implicit Arguments.
Require Import Morphisms Lia FinFun.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import 
  prelim terms syntax semantics confluence. 


Set Default Proof Using "Type".

(* * Equational Theory *)
Section Equivalence.
  Context {X: Const}.
  Notation "s ≡ t" := (equiv (@step X) s t) (at level 70).


  (* ** Compatibility Properties *)
  Section CompatibilityProperties.
    
    Global Instance equiv_lam_proper:
      Proper (equiv step ++> equiv step) (@lam X).
    Proof.
      intros ? ? (v & H1 & H2) % church_rosser; eauto. 
      rewrite H1, H2. reflexivity. 
    Qed.


    Global Instance equiv_app_proper:
      Proper (equiv step ++> equiv step ++> equiv step) (@app X).
    Proof.
      intros ? ? (v & H1 & H2) % church_rosser ? ? (v' & H3 & H4) % church_rosser;
        eauto.
      rewrite H1, H2, H3, H4. reflexivity.
    Qed.

    Lemma ren_equiv s t delta:
      s ≡ t -> ren delta s ≡ ren delta t.
    Proof.
      intros (v & ? & ?) % church_rosser; eauto.
      transitivity (ren delta v); [| symmetry].
      all: eapply equiv_star, ren_steps; eauto.
    Qed.

    Global Instance ren_equiv_proper:
      Proper (eq ++> equiv step ++> equiv step) (@ren X).
    Proof.
      intros ? zeta -> s t H; now eapply ren_equiv.
    Qed.
    
    Lemma subst_equiv s t sigma:
      s ≡ t -> sigma • s ≡ sigma • t.
    Proof.
      intros (v & ? & ?) % church_rosser; eauto.
      transitivity (sigma • v); [| symmetry].
      all: eapply equiv_star, subst_steps; eauto.
    Qed.

    Global Instance subst_equiv_proper:
      Proper (eq ++> equiv step ++> equiv step) (@subst_exp X).
    Proof.
      intros ? zeta -> s t H; now eapply subst_equiv.
    Qed.

    Lemma subst_pointwise_equiv (s: exp X) sigma tau:
      (forall x, x ∈ vars s -> sigma x ≡ tau x) -> sigma • s ≡ tau • s.
    Proof.
      induction s in sigma, tau |-*; cbn -[vars]; eauto.
      - intros H; eapply equiv_lam_proper, IHs.
        intros []; cbn -[vars]. reflexivity.
        intros ? % vars_varof % varofLambda % varof_vars % H.
        unfold funcomp.
        now eapply ren_equiv.
      - intros H; rewrite IHs1, IHs2; eauto.
    Qed.

  End CompatibilityProperties.

  (* ** Injectivity Properties *)
  Section InjectivityProperties.

    Lemma equiv_var_eq (x y: fin):
      var x ≡ var y -> x = y.
    Proof.
      intros; eapply equiv_unique_normal_forms in H; eauto.
      congruence.
    Qed.
      
    Lemma equiv_const_eq (x y: X):
      const x ≡ const y -> x = y.
    Proof.
      intros; eapply equiv_unique_normal_forms in H; eauto.
      congruence.
    Qed.

    Lemma equiv_lam_elim (s t: exp X):
      lambda s ≡ lambda t -> s ≡ t.
    Proof.
      intros (v & [] %steps_lam & [] %steps_lam) % church_rosser; intuition; subst.
      injection H as ->; eauto. 
    Qed.

    Lemma equiv_app_elim (s s' t t': exp X):
      s t ≡ s' t' ->  isAtom (head s) -> isAtom (head s') -> s ≡ s' /\ t ≡ t'.
    Proof.
      intros (v & [] % steps_app & [] % steps_app) % church_rosser H3; eauto.
      * do 2 destruct H, H0; intuition; subst;
          injection H as -> ->; eauto.
      * do 2 destruct H; destruct H0; intuition; subst.
        all: destruct (head s'); cbn in *; intuition.
      * do 2 destruct H0; destruct H; intuition; subst.
        all: destruct (head s); cbn in *; intuition.
      * destruct H, H0; intuition.
        all: destruct (head s); cbn in *; intuition.
    Qed.

    Lemma equiv_anti_ren delta (s t: exp X):
      Injective delta -> ren delta s ≡ ren delta t -> s ≡ t.
    Proof.
      intros ? (v & H1 & H2) % church_rosser; eauto.
      eapply steps_anti_ren in H1 as [].
      eapply steps_anti_ren in H2 as [].
      intuition; subst.
      eapply anti_ren in H4; eauto.
      subst; eauto. 
    Qed.
  
  End InjectivityProperties.

  (* ** Disjointness Properties *)
  Section DisjointnessProperties.

    Lemma equiv_neq_var_app (x: nat) (s t: exp X):
      var x ≡ s t -> isAtom (head s) -> False.
    Proof.
      intros EQ.
      destruct (head s) as [y | | | ] eqn: H'; intuition.                   
      all: eapply church_rosser in EQ as (v & L & R); eauto.
      all: inv L; firstorder using normal_var.  
      all: eapply steps_app in R as [R|R].
      1, 3: destruct R as (? & ? & ? & ?); discriminate.
      all:  destruct R; intuition; rewrite H' in *; syn.
    Qed.

    Lemma equiv_neq_lambda_app (s' s t: exp X):
      lambda s' ≡ s t -> isAtom (head s) -> False.
    Proof.
      intros EQ. 
      destruct (head s) as [y | | | ] eqn: H'; intuition. 
      all: eapply church_rosser in EQ as (v & L & R); eauto.
      all: eapply steps_lam in L as (v' & ? & ?); subst. 
      all: eapply steps_app in R as [R|R].
      1, 3: destruct R as (? & ? & ? & ?); discriminate.
      all: destruct R; intuition; rewrite H' in *; syn.
    Qed.

    Lemma equiv_neq_var_lambda (x: nat) s: ~ var x ≡ lambda s.
    Proof.
      intros (v & ? & ?) % church_rosser; eauto.
      inv H; firstorder using normal_var.
      eapply steps_lam in H0 as []; intuition; discriminate.
    Qed.

    Lemma equiv_neq_var_const (x: nat) c: ~ var x ≡ const c.
    Proof.
      intros (v & ? & ?) % church_rosser; eauto.
      inv H; firstorder using normal_var.
      inv H0. inv H.
    Qed.


    Lemma equiv_neq_const_lam  s c: ~ const c ≡ lambda s.
    Proof.
      intros (v & ? & ?) % church_rosser; eauto.
      inv H; firstorder using normal_var.
      eapply steps_lam in H0 as []; intuition; discriminate.
      inv H1. 
    Qed.

    Lemma equiv_neq_const_app (s t: exp X) c:
      const c ≡ s t -> isAtom (head s) -> False.
    Proof.
      intros EQ.
      destruct (head s) as [y | | | ] eqn: H'; intuition.                   
      all: eapply church_rosser in EQ as (v & L & R); eauto.
      all: inv L; firstorder using normal_const.  
      all: eapply steps_app in R as [R|R].
      1, 3: destruct R as (? & ? & ? & ?); discriminate.
      all:  destruct R; intuition; rewrite H' in *; syn.
    Qed.

  End DisjointnessProperties.


  (* ** Huet Definition *)
  Section HuetDefinition.
    Variable (s t v1 v2: exp X).
    Hypothesis (E1: s ▷ v1) (E2: t ▷ v2).


    Lemma equiv_huet_forward:
      s ≡ t ->  v1 = v2.
    Proof using E1 E2.
      destruct E1 as [H1 N1], E2 as [H2 N2].
      intros H; eapply equiv_unique_normal_forms; eauto.
      now rewrite <-H1, <-H2.  
    Qed.

    Lemma equiv_huet_backward:
      v1 = v2 -> s ≡ t.
    Proof using E1 E2.
      intros; subst; destruct E1, E2; eapply equiv_join; eauto. 
    Qed.
  End HuetDefinition.


End Equivalence.

Notation "s ≡ t" := (equiv step s t) (at level 70).  

Hint Resolve equiv_neq_var_app equiv_neq_var_lambda equiv_neq_var_const
     equiv_neq_const_app equiv_neq_const_lam equiv_neq_lambda_app : core.



Ltac ClearRefl H :=
  let T := type of H in
  match T with
  | ?X ≡ ?X => clear H
  | _ => idtac
  end.

Ltac Injection H :=
  let T := type of H in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  match T with
  | var _ ≡ var _ => eapply equiv_var_eq in H as H1; ClearRefl H1
  | const _ ≡ const _ => eapply equiv_const_eq in H as H1; ClearRefl H1
  | lambda _ ≡ lambda _ => eapply equiv_lam_elim in H as H1; ClearRefl H1
  | app _ _ ≡ app _ _ =>  eapply equiv_app_elim in H as [H1 H2]; [| atom..]; ClearRefl H1; ClearRefl H2
  end.



Ltac Discriminate :=
  match goal with
  | [H: var _ ≡ const _ |- _] => eapply equiv_neq_var_const in H as []
  | [H: const _ ≡ var _ |- _] => symmetry in H; eapply equiv_neq_var_const in H as []
  | [H: var _ ≡ app _ _ |- _] => solve [eapply equiv_neq_var_app in H as []; atom]                        
  | [H: app _ _ ≡ var _ |- _] => solve [symmetry in H; eapply equiv_neq_var_app in H as []; atom]
  | [H: var _ ≡ lambda _ |- _] => eapply equiv_neq_var_lambda in H as []
  | [H: lambda _ ≡ var _ |- _] => symmetry in H; eapply equiv_neq_var_lambda in H as []
  | [H: const _ ≡ lambda _ |- _] => eapply equiv_neq_const_lam in H as []
  | [H: lambda _ ≡ const _ |- _] => symmetry in H; eapply equiv_neq_const_lam in H as []
  | [H: const _ ≡ app _ _ |- _] => solve [eapply equiv_neq_const_app in H as []; atom]
  | [H: app _ _ ≡ const _ |- _] => solve [symmetry in H; eapply equiv_neq_const_app in H as []; atom]
  | [H: lambda _ ≡ app _ _ |- _] => solve [eapply equiv_neq_lambda_app in H as []; atom]
  | [H: app _ _ ≡ lambda _ |- _] => solve [symmetry in H; eapply equiv_neq_lambda_app in H as []; atom]
  | [H: var _ ≡ var _ |- _] => solve [eapply equiv_var_eq in H as ?; discriminate]
  | [H: const _ ≡ const _ |- _] => solve [eapply equiv_const_eq in H as ?; discriminate]
  end.


Lemma equiv_head_equal X (s t: exp X):
  s ≡ t -> isAtom (head s) -> isAtom (head t) -> head s = head t.
Proof.
  induction s in t |-*; destruct t; intros; try Discriminate; Injection H; subst; eauto.
  - cbn in *; intuition.
  - cbn; eapply IHs1; eauto. 
Qed. 
