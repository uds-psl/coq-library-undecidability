(** * Categoricity of PA2 *)

Require Import PeanoNat Lia Vector.
From Undecidability.SOL Require Import SOL PA2.
From Equations.Prop Require Import DepElim.
From Undecidability.SOL.Util Require Import VectorUtil Syntax Subst Tarski PA2_facts.

Import VectorNotations SubstNotations.


Section Categoricity.

  Variable M1 : Model.
  Variable M2 : Model.

  Hypothesis M1_correct : M1 ⊨ PA2.
  Hypothesis M2_correct : M2 ⊨ PA2.

  (** Abbreviations *)
  Notation D1 := (M_domain M1).
  Notation D2 := (M_domain M2).
  Notation I1 := (M_interp M1).
  Notation I2 := (M_interp M2).
  Notation eq1_sem := (eq_sem M1).
  Notation eq2_sem := (eq_sem M2).

  Notation "'O1'" := (@i_f _ _ D1 I1 Zero ([])).
  Notation "'O2'" := (@i_f _ _ D2 I2 Zero ([])).
  Notation "'S1' x" := (@i_f _ _ D1 I1 Succ ([x])) (at level 37).
  Notation "'S2' x" := (@i_f _ _ D2  I2 Succ ([x])) (at level 37).
  Notation "x 'i⊕1' y" := (@i_f _ _ D1 I1 Plus ([x ; y])) (at level 39).
  Notation "x 'i⊕2' y" := (@i_f _ _ D2 I2 Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗1' y" := (@i_f _ _ D1 I1 Mult ([x ; y])) (at level 38).
  Notation "x 'i⊗2' y" := (@i_f _ _ D2 I2 Mult ([x ; y])) (at level 38).
  Notation "x '=1=' y" := (@i_P _ _ D1 I1 Eq ([x ; y])) (at level 40).
  Notation "x '=2=' y" := (@i_P _ _ D2 I2 Eq ([x ; y])) (at level 40).


  (** Definition of isomorphism *)
  Inductive F : D1 -> D2 -> Prop :=
    | F_O : F O1 O2
    | F_S : forall x y, F x y -> F (S1 x) (S2 y).


  Lemma F_inv1 x :
    F (S1 x) O2 -> False.
  Proof.
    intros H. inversion H.
    + now apply (zero_succ M1 M1_correct x).
    + now apply (zero_succ M2 M2_correct y).
  Qed.

  Lemma F_inv2 y :
    F O1 (S2 y) -> False.
  Proof.
    intros H. inversion H.
    + now apply (zero_succ M2 M2_correct y).
    + now apply (zero_succ M1 M1_correct x).
  Qed.

  Lemma F_inv3 y :
    F O1 y -> y = O2.
  Proof.
    destruct (case_analysis M2 M2_correct y) as [->|[y' ->]].
    - easy.
    - now intros H%F_inv2.
  Qed.

  Lemma F_inv4 x :
    F x O2 -> x = O1.
  Proof.
    destruct (case_analysis M1 M1_correct x) as [->|[x' ->]].
    - easy.
    - now intros H%F_inv1.
  Qed.

  Lemma F_inv5 :
    forall x y, F (S1 x) y -> exists y', y = S2 y'.
  Proof.
    intros x y. destruct (case_analysis M2 M2_correct y) as [->|[y' ->]].
    - now intros H%F_inv1.
    - intros _. now exists y'.
  Qed.

  Lemma F_inv6 :
    forall x y, F x (S2 y) -> exists x', x = S1 x'.
  Proof.
    intros x y. destruct (case_analysis M1 M1_correct x) as [->|[x' ->]].
    - now intros H%F_inv2.
    - intros _. now exists x'.
  Qed.

  Lemma F_inv7 x y :
    F (S1 x) (S2 y) -> F x y.
  Proof.
    intros H. inversion H.
    + exfalso. now apply (zero_succ M1 M1_correct x).
    + apply (succ_inj M1 M1_correct) in H0 as ->.
      apply (succ_inj M2 M2_correct) in H1 as ->.
      exact H2.
  Qed.


  Lemma F_total :
    forall x, exists y, F x y.
  Proof.
    apply (induction M1 M1_correct).
    - exists O2. exact F_O.
    - intros x [y IH]. exists (S2 y). now apply F_S.
  Qed.

  Lemma F_surjective :
    forall y, exists x, F x y.
  Proof.
    apply (induction M2 M2_correct).
    - exists O1. exact F_O.
    - intros y [x IH]. exists (S1 x). now apply F_S.
  Qed.

  Lemma F_functional :
    forall x y y', F x y -> F x y' -> y = y'.
  Proof.
    apply (induction M1 M1_correct (fun x => forall y y', F x y -> F x y' -> y = y')).
    - intros y y' H1 H2. now rewrite (F_inv3 y), (F_inv3 y').
    - intros x IH y y' H1 H2. 
      destruct (F_inv5 x y H1) as [z ->], (F_inv5 x y' H2) as [z' ->].
      apply F_inv7 in H1; apply F_inv7 in H2. now rewrite (IH z z').
  Qed.

  Lemma F_injective :
    forall x x' y, F x y -> F x' y -> x = x'.
  Proof.
    intros x x' y. revert y x x'. 
    apply (induction M2 M2_correct (fun y => forall x x', F x y -> F x' y -> x = x')).
    - intros x x'' H1 H2. now rewrite (F_inv4 x), (F_inv4 x'').
    - intros y IH x x' H1 H2. 
      destruct (F_inv6 x y H1) as [z ->], (F_inv6 x' y H2) as [z' ->].
      apply F_inv7 in H1; apply F_inv7 in H2. now rewrite (IH z z').
  Qed.


  Lemma F_add :
    forall x x' y y', F x y -> F x' y' -> F (x i⊕1 x') (y i⊕2 y').
  Proof.
    apply (induction M1 M1_correct (fun x => forall x' y y', F x y -> F x' y' -> F (x i⊕1 x') (y i⊕2 y'))).
    - intros x' y y' H1 H2. rewrite (F_inv3 y H1).
      now rewrite (add_zero M1), (add_zero M2).
    - intros x'' IH x' y y' H1 H2. destruct (F_inv5 x'' y H1) as [y'' ->].
      rewrite (add_rec M1), (add_rec M2); try easy.
      apply F_S, IH. now apply F_inv7. exact H2.
  Qed.

  Lemma F_mul :
    forall x x' y y', F x y -> F x' y' -> F (x i⊗1 x') (y i⊗2 y').
  Proof.
    apply (induction M1 M1_correct (fun x => forall x' y y', F x y -> F x' y' -> F (x i⊗1 x') (y i⊗2 y'))).
    - intros x' y y' H1 H2. rewrite (F_inv3 y H1).
      rewrite (mul_zero M1), (mul_zero M2); try easy.
      exact F_O.
    - intros x'' IH x' y y' H1 H2. destruct (F_inv5 x'' y H1) as [y'' ->].
      rewrite (mul_rec M1), (mul_rec M2); try easy.
      apply F_add. exact H2. apply IH. now apply F_inv7. exact H2.
  Qed.

  Lemma F_eq :
    forall x x' y y', F x y -> F x' y' -> (x =1= x' <-> y =2= y').
  Proof.
    apply (induction M1 M1_correct (fun x => forall x' y y', F x y -> F x' y' -> (x =1= x' <-> y =2= y'))).
    - intros x' y y' H1 H2. split. 
      + intros H3%eq1_sem. rewrite <- H3 in H2. rewrite (F_inv3 y H1). 
        rewrite (F_inv3 y' H2). now apply eq2_sem. easy.
      + intros H3%eq2_sem. rewrite <- H3 in H2. rewrite (F_inv3 y H1) in H2. 
        rewrite (F_inv4 x' H2). now apply eq1_sem. easy.
    - intros x IH x' y y' H1 H2. split.
      + intros H3%eq1_sem. rewrite <- H3 in H2.
        destruct (F_inv5 x y H1) as [z ->]. destruct (F_inv5 x y' H2) as [z' ->].
        enough (z =2= z') as ->%eq2_sem by (try easy; now apply eq2_sem).
        apply (IH x). now apply F_inv7. now apply F_inv7. now apply eq1_sem. easy.
      + intros H3%eq2_sem. rewrite <- H3 in H2.
        destruct (F_inv5 x y H1) as [z ->]. destruct (F_inv6 x' z H2) as [x'' ->].
        enough (x =1= x'') as ->%eq1_sem by (try easy; now apply eq1_sem).
        apply (IH x'' z z). now apply F_inv7. now apply F_inv7. now apply eq2_sem. easy.
  Qed.



  (** F describes an isomorphism between D1 and D2. *)

  Class Iso T1 T2 := { iso : T1 -> T2 -> Prop }.
  Notation "rho ≈ sigma" := (iso rho sigma) (at level 30).

  Instance Iso_indi : Iso D1 D2 := {| 
    iso := F 
  |}.
  Instance Iso_vec ar : Iso (vec D1 ar) (vec D2 ar) := {| 
    iso v1 v2 := @Forall2 _ _ F ar v1 v2
  |}.
  Instance Iso_func {ar} : Iso (vec D1 ar -> D1) (vec D2 ar -> D2) := {| 
    iso f1 f2 := forall v1 v2, v1 ≈ v2 -> F (f1 v1) (f2 v2)
  |}.
  Instance Iso_pred {ar} : Iso (vec D1 ar -> Prop) (vec D2 ar -> Prop) := {| 
    iso P1 P2 := forall v1 v2, v1 ≈ v2 -> (P1 v1 <-> P2 v2)
  |}.
  Instance Iso_env : Iso (env D1) (env D2) := {| 
    iso rho1 rho2 := forall n, 
         get_indi rho1 n ≈ get_indi rho2 n
       /\ forall ar, get_func rho1 n ar ≈ get_func rho2 n ar
                  /\ get_pred rho1 n ar ≈ get_pred rho2 n ar
  |}.


  Lemma iso_env_i rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p x y :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈ ⟨rho2_i, rho2_f, rho2_p⟩ -> x ≈ y -> ⟨x .: rho1_i, rho1_f, rho1_p⟩ ≈ ⟨y .: rho2_i, rho2_f, rho2_p⟩.
  Proof.
    intros H1 H2. split. destruct n; firstorder. apply H1.
  Qed.

  Lemma iso_env_f rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p ar (f1 : vec D1 ar -> D1) f2 :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈ ⟨rho2_i, rho2_f, rho2_p⟩ -> f1 ≈ f2 -> ⟨rho1_i, f1 .: rho1_f, rho1_p⟩ ≈ ⟨rho2_i, f2 .: rho2_f, rho2_p⟩.
  Proof.
    intros H1 H2. split. apply H1. intros ar'. split. 2: apply H1.
    destruct n; cbn; destruct (PeanoNat.Nat.eq_dec ar ar') as [->|].
    apply H2. all: apply H1.
  Qed.

  Lemma iso_env_p rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p ar (P1 : vec D1 ar -> Prop) P2 :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈ ⟨rho2_i, rho2_f, rho2_p⟩ -> P1 ≈ P2 -> ⟨rho1_i, rho1_f, P1 .: rho1_p⟩ ≈ ⟨rho2_i, rho2_f, P2 .: rho2_p⟩.
  Proof.
    intros H1 H2. split. apply H1. intros ar'. split. apply H1.
    destruct n; cbn; destruct (PeanoNat.Nat.eq_dec ar ar') as [->|].
    apply H2. all: apply H1.
  Qed.


  Lemma iso_vec_eq1 ar (v1 v1' : vec D1 ar) v2 :
    v1 ≈ v2 -> v1' ≈ v2 -> v1 = v1'.
  Proof.
    intros H1 H2. induction v1; dependent elimination v1'. 
    reflexivity. f_equal. eapply F_injective. apply H1. apply H2.
    eapply IHv1. apply H1. apply H2.
  Qed.

  Lemma iso_vec_eq2 ar (v1 : vec D1 ar) v2 v2' :
    v1 ≈ v2 -> v1 ≈ v2' -> v2 = v2'.
  Proof.
    intros H1 H2. induction v2; dependent elimination v2'; dependent elimination v1. 
    reflexivity. f_equal. eapply F_functional. apply H1. apply H2.
    eapply IHv2. apply H1. apply H2.
  Qed.



  (** We can translate predicates along this isomorphism *)

  Lemma P1_to_P2 ar (P1 : vec D1 ar -> Prop) :
    { P2 | P1 ≈ P2 }.
  Proof.
    exists (fun v => forall v', Forall2 F v' v -> P1 v').
    intros v1 v2 H1. split.
    - intros H2 v' H3. induction v'; dependent elimination v1.
      + exact H2.
      + assert (h = h0) as ->. { apply eq1_sem. easy. eapply F_eq. apply H3. apply H1. now apply eq2_sem. }
        assert (v' = t0) as ->. { eapply IHv'. apply H1. reflexivity. apply H3. } 
        exact H2.
    - firstorder.
  Qed.

  Lemma P2_to_P1 ar (P2 : vec D2 ar -> Prop) :
    { P1 | P1 ≈ P2 }.
  Proof.
    exists (fun v => forall v', Forall2 F v v' -> P2 v').
    intros v1 v2 H1. split.
    - firstorder.
    - intros H2 v' H3. induction v'; dependent elimination v2.
      + exact H2.
      + dependent elimination v1.
        assert (h = h0) as ->. { apply eq2_sem. easy. eapply F_eq. apply H3. apply H1. now apply eq1_sem. }
        assert (v' = t0) as ->. { eapply IHv'. apply H1. reflexivity. apply H3. } 
        exact H2.
  Qed.


  (** Vectors and functions can not be computationally translated 
      because of the elim restriction. But we can prove existential
      versions. *)

  Lemma v1_to_v2_ex ar (v1 : vec D1 ar) :
    exists v2, v1 ≈ v2.
  Proof.
    induction v1.
    - now exists [].
    - destruct IHv1 as [v2 IH]. destruct (F_total h) as [y H]. 
      now exists (y::v2).
  Qed.

  Lemma v2_to_v1_ex ar (v2 : vec D2 ar) :
    exists v1, v1 ≈ v2.
  Proof.
    induction v2.
    - now exists [].
    - destruct IHv2 as [v1 IH]. destruct (F_surjective h) as [x H]. 
      now exists (x::v1).
  Qed.


  (** The isomorphism also respects evaluation of terms under
      isomorphic environments *)

  Lemma F_term rho1 rho2 t :
    rho1 ≈ rho2 -> F (eval rho1 t) (eval rho2 t).
  Proof.
    revert t. apply (term_ind (fun t => rho1 ≈ rho2 -> F (eval rho1 t) (eval rho2 t))); intros.
    - apply H.
    - apply H, Forall2_Forall. induction v. easy.
      split. now apply IH. apply IHv, IH.
    - destruct f; repeat depelim v; cbn in *.
      + exact F_O.
      + apply F_S. now apply IH.
      + apply F_add; now apply IH.
      + apply F_mul; now apply IH.
  Qed.


  (** A similar result holds for satisfiablility of formulas, but
      as we are not able to computationally translate functions along 
      the isomorphism, we must restrict to formulas without function
      quantificaion.
      To make our lives easier for the incompleteness proof, we 
      restrict even further to only first-order formulas *)

  Definition iso_env_funcfree (rho1 : env D1) rho2 := forall n, get_indi rho1 n ≈ get_indi rho2 n /\ forall ar, get_pred rho1 n ar ≈ get_pred rho2 n ar.
  Notation "rho ≈FF sigma" := (iso_env_funcfree rho sigma) (at level 30).

  Lemma iso_env_funcfree_i rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p x y :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈FF ⟨rho2_i, rho2_f, rho2_p⟩ -> x ≈ y -> ⟨x .: rho1_i, rho1_f, rho1_p⟩ ≈FF ⟨y .: rho2_i, rho2_f, rho2_p⟩.
  Proof.
    intros H1 H2 n. split. destruct n; firstorder. apply H1.
  Qed.

  Lemma iso_env_funcfree_p rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p ar (P1 : vec D1 ar -> Prop) P2 :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈FF ⟨rho2_i, rho2_f, rho2_p⟩ -> P1 ≈ P2 -> ⟨rho1_i, rho1_f, P1 .: rho1_p⟩ ≈FF ⟨rho2_i, rho2_f, P2 .: rho2_p⟩.
  Proof.
    intros H1 H2 n. split. apply H1. intros ar'. destruct n; cbn;
    destruct Nat.eq_dec as [->|]. apply H2. all: apply H1.
  Qed.

  Lemma F_term_funcfree rho1 rho2 t :
    rho1 ≈FF rho2 -> funcfreeTerm t -> F (eval rho1 t) (eval rho2 t).
  Proof.
    induction t; intros.
    - apply H.
    - easy.
    - destruct f; repeat depelim v; cbn in *.
      + exact F_O.
      + apply F_S. now apply IH.
      + apply F_add; now apply IH.
      + apply F_mul; now apply IH.
  Qed.

  Theorem sat_iff_funcfree rho1 rho2 phi : 
    rho1 ≈FF rho2 -> funcfree phi -> rho1 ⊨ phi <-> rho2 ⊨ phi.
  Proof.
    revert phi rho1 rho2. induction phi; intros rho1 rho2 H F; cbn.
    - easy.
    - destruct p; cbn.
      + apply H. induction v; cbn. easy. split. apply F_term_funcfree. apply H. 
        apply F. apply IHv, F. 
      + destruct P; repeat depelim v; cbn in *. now apply F_eq; apply F_term_funcfree.
    - destruct F as [F1 F2]. 
      specialize (IHphi1 rho1 rho2 H F1); specialize (IHphi2 rho1 rho2 H F2).
      destruct b; tauto.
    - destruct q; split.
      + intros H1 y. destruct (F_surjective y).
        eapply IHphi. 2: easy. 2: apply H1. apply iso_env_funcfree_i; eauto.
      + intros H1 x. destruct (F_total x).
        eapply IHphi. 2: easy. 2: apply H1. apply iso_env_funcfree_i; eauto.
      + intros [x H1]. destruct (F_total x) as [y]. exists y.
        eapply IHphi. 2: easy. 2: apply H1. apply iso_env_funcfree_i; eauto.
      + intros [y H1]. destruct (F_surjective y) as [x]. exists x.
        eapply IHphi. 2: easy. 2: apply H1. apply iso_env_funcfree_i; eauto.
    - easy.
    - destruct q; split.
      + intros H1 P2. destruct (P2_to_P1 _ P2) as [P1 H2].
        eapply IHphi. 3: apply H1. apply iso_env_funcfree_p; eauto. easy.
      + intros H1 P1. destruct (P1_to_P2 _ P1) as [P2 H2].
        eapply IHphi. 3: apply H1. apply iso_env_funcfree_p; eauto. easy.
      + intros [P1 H1]. destruct (P1_to_P2 _ P1) as [P2 H2]. exists P2.
        eapply IHphi. 3: apply H1. apply iso_env_funcfree_p; eauto. easy.
      + intros [P2 H1]. destruct (P2_to_P1 _ P2) as [P1 H2]. exists P1.
        eapply IHphi. 3: apply H1. apply iso_env_funcfree_p; eauto. easy.
  Qed.

End Categoricity.



(** Consequence of categoricity we will use for undecidability:
    If a closed formula holds in one model, it holds in all models. *)

Theorem PA2_models_agree phi M rho:
  funcfree phi -> bounded_indi 0 phi -> (forall ar, bounded_pred ar 0 phi) 
  -> M ⊨ PA2 -> (M, rho) ⊨ phi -> forall M', M' ⊨ PA2 -> M' ⊨ phi.
Proof.
  intros F Bi Bp MPA2 H M' M'PA2 rho'.
  eapply sat_ext_closed_funcfree with (sigma := empty_PA2_env _); try assumption.
  eapply sat_ext_closed_funcfree with (sigma := empty_PA2_env _) in H; try assumption.
  eapply sat_iff_funcfree. 5: apply H. apply M'PA2. apply MPA2.
  intros n. split. apply F_O. cbn. reflexivity. assumption.
Qed.

Theorem PA2_models_agree_FO phi M rho :
  first_order phi -> bounded_indi 0 phi -> M ⊨ PA2 -> (M, rho) ⊨ phi -> forall M', M' ⊨ PA2 ->  M' ⊨ phi.
Proof.
  intros F B MPA2 H M' M'PA2 rho'.
  eapply sat_ext_closed_FO with (sigma := empty_PA2_env _); try assumption.
  eapply sat_ext_closed_FO with (sigma := empty_PA2_env _) in H; try assumption.
  eapply sat_iff_funcfree. 5: apply H. apply M'PA2. apply MPA2.
  intros n. split. apply F_O. cbn. reflexivity. now apply firstorder_funcfree.
Qed.


Notation "rho ≈ sigma" := (@iso _ _ _ rho sigma) (at level 30).
Notation "rho ≈FF sigma" := (@iso_env_funcfree _ _ rho sigma) (at level 30).
