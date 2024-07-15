Require Import Relations PeanoNat.

Require Undecidability.L.L.
Import L (term, var, app, lam).

From Undecidability.LambdaCalculus Require Import Lambda Util.facts.

#[local] Unset Implicit Arguments.

Set Default Goal Selector "!".

Section Basics.
  Context {X : Type}.
  Definition joinable (R : X -> X -> Prop) x y := exists z, R x z /\ R y z.
  Definition diamond (R : X -> X -> Prop) := forall x y z, R x y -> R x z -> joinable R y z.
  Definition confluent (R : X -> X -> Prop) := diamond (clos_refl_trans X R).
  Definition reflexive (R : X -> X -> Prop) := forall x, R x x.
  Definition semi_confluent R := forall x y z, R x y -> clos_refl_trans X R x z -> joinable (clos_refl_trans X R) y z.
  Notation "R <<= S" := (inclusion _ R S) (at level 70).
  Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).

  Fact inclusion_mono R S : R <<= S ->
    clos_refl_trans X R <<= clos_refl_trans X S.
  Proof.
    intros H x y H'. induction H'.
    - now apply rt_step, H.
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Fact diamond_semi_confluent R :
    diamond R -> semi_confluent R.
  Proof.
    intros H x y1 y2 H1 H2 % clos_rt_rt1n_iff. revert y1 H1.
    induction H2 as [x|x x' y2 H2 _ IH]; intros y1 H1.
    - exists y1; eauto using clos_refl_trans.
    - assert (joinable R y1 x') as [z [H3 H4]].
      { eapply H; eauto. }
      assert (joinable (clos_refl_trans _ R) z y2) as [u [H5 H6]].
      { apply IH; auto. }
      exists u; eauto using clos_refl_trans.
  Qed.

  Fact confluent_semi R :
    confluent R <-> semi_confluent R.
  Proof.
    split.
    - intros H x y1 y2 H1 H2.
      eapply H; [|exact H2]. eauto using clos_refl_trans. 
    - intros H x y1 y2 H1 % clos_rt_rt1n_iff H2. revert y2 H2.
      induction H1 as [x|x x' y1 H1 _ IH]; intros y2 H2.
      + exists y2; eauto using clos_refl_trans.
      + assert (joinable (clos_refl_trans _ R) x' y2) as [z [H3 H4]].
        { eapply H; eauto. }
        assert (joinable (clos_refl_trans _ R) y1 z) as [u [H5 H6]].
        { apply IH; auto. }
        exists u; eauto using clos_refl_trans.
  Qed.

  Fact diamond_confluent R :
    diamond R -> confluent R.
  Proof.
    intros H.
    apply confluent_semi, diamond_semi_confluent, H.
  Qed.

  Fact diamond_ext R S:
    R === S -> diamond S -> diamond R.
  Proof.
    intros H1 H2 x y z H3 H4.
    assert (joinable S y z); firstorder.
  Qed.
End Basics.


Section Takahashi.
  Variables (X: Type)  (R: X -> X -> Prop).
  Implicit Types (x y z : X).
  Notation "x > y" := (R x y) (at level 70).
  Notation "x >* y" := (clos_refl_trans X R x y) (at level 60).

  Definition tak_fun rho := forall x y, x > y -> y > rho x.

  Variables (rho: X -> X) (tak: tak_fun rho).

  Fact tak_diamond :
    diamond R.
  Proof using tak rho.
    intros x y z H1 % tak H2 % tak. now exists (rho x).
  Qed.

  Fact tak_sound x :
    reflexive R -> x > rho x.
  Proof using tak.
    intros H. apply tak, H.
  Qed.

  Fact tak_mono x y :
    x > y -> rho x > rho y.
  Proof using tak.
    intros H % tak % tak. exact H.
  Qed.

  Fact tak_mono_n x y n :
    x > y -> Nat.iter n rho x > Nat.iter n rho y.
  Proof using tak.
    intros H. induction n; cbn; auto using tak_mono.
  Qed.

  Fact tak_cofinal x y :
    x >* y -> exists n, y >* Nat.iter n rho x.
  Proof using tak.
    intros H % clos_rt_rt1n_iff. induction H as [x|x z y H _ [n IH]].
    - exists 0. apply rt_refl.
    - exists (S n). eapply rt_trans.
      + eassumption.
      + rewrite Nat.iter_succ_r. apply rt_step. now apply tak_mono_n, tak.
  Qed.

End Takahashi.

Section TMT.
  Notation "R <<= S" := (inclusion _ R S) (at level 70).
  Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).

  Variables (X: Type) (R S: X -> X -> Prop)
            (H1: R <<= S) (H2: S <<= clos_refl_trans X R).

  Fact sandwich_equiv :
    clos_refl_trans X R === clos_refl_trans X S.
  Proof using H1 H2.
    split.
    - now apply inclusion_mono.
    - intros x y H3. apply inclusion_mono in H2.
      now apply clos_rt_idempotent, H2.
  Qed.

  Fact sandwich_confluent :
    diamond S -> confluent R.
  Proof using H1 H2.
    intros H3 % diamond_confluent.
    revert H3. apply diamond_ext, sandwich_equiv; auto.
  Qed.

  Theorem TMT rho :
    reflexive S -> tak_fun X S rho -> confluent R.
  Proof using H1 H2.
    intros H3 H4. 
    eapply sandwich_confluent, tak_diamond, H4.
  Qed.

End TMT.
