From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts MoreEnumerabilityFacts.
From Undecidability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

(** ** Definitions *)

Infix "⪯ᵢ" := inf_reduces (at level 70).

(** ** Pre-order properties *)

Section Properties.

  Variables (X : Type) (P : X -> Prop)
            (Y : Type) (Q : Y -> Prop)
            (Z : Type) (R : Z -> Prop).

  Fact reduces_reflexive : P ⪯ P.
  Proof. exists (fun x => x); red; tauto. Qed.

  Fact ireduces_reflexive : P ⪯ᵢ P.
  Proof. exists (fun x => x); red; tauto. Qed.

  Fact reduces_transitive : P ⪯ Q -> Q ⪯ R -> P ⪯ R.
  Proof.
    unfold reduces, reduction.
    intros (f & Hf) (g & Hg).
    exists (fun x => g (f x)).
    intro; rewrite Hf, Hg; tauto.
  Qed.

  Fact ireduces_transitive : P ⪯ᵢ Q -> Q ⪯ᵢ R -> P ⪯ᵢ R.
  Proof.
    unfold inf_reduces, reduction.
    intros (f & Hf) (g & Hg).
    exists (fun x => g (f x)).
    intro; rewrite Hf, Hg; tauto.
  Qed.

  Fact ireduces_reduces : P ⪯ᵢ Q -> P ⪯ Q.
  Proof. intros (f & ?); exists f; auto. Qed.

  Fact reduces_ireduces : P ⪯ Q -> inhabited (P ⪯ᵢ Q).
  Proof. intros (f & ?); exists; exists f; auto. Qed.

  Fact reduces_ireduces_iff : P ⪯ Q <-> inhabited (P ⪯ᵢ Q).
  Proof.
    split.
    + apply reduces_ireduces.
    + intros []; apply ireduces_reduces; auto.
  Qed.

  (** ** An equivalent dependent definition *)

  Fact ireduces_dependent :
         (P ⪯ᵢ Q -> forall x, { y | P x <-> Q y })
       * ((forall x, { y | P x <-> Q y }) -> P ⪯ᵢ Q).
  Proof.
    unfold inf_reduces, reduction.
    split.
    + intros (f & Hf).
      intros x; exists (f x); auto.
    + intros f.
      exists (fun x => proj1_sig (f x)).
      intros; apply (proj2_sig (f x)).
  Qed.

End Properties.

Lemma dec_red X (p : X -> Prop) Y (q : Y -> Prop) :
  p ⪯ q -> decidable q -> decidable p.
Proof.
  unfold decidable, decider, reduces, reduction, reflects.
  intros [f] [d]. exists (fun x => d (f x)). intros x. rewrite H. eapply H0.
Qed.

Lemma red_comp X (p : X -> Prop) Y (q : Y -> Prop) :
  p ⪯ q -> (fun x => ~ p x) ⪯ (fun y => ~ q y).
Proof.
  intros [f]. exists f. intros x. red in H. now rewrite H.
Qed.

Section enum_red.

  Variables (X Y : Type) (p : X -> Prop) (q : Y -> Prop).
  Variables (f : X -> Y) (Hf : forall x, p x <-> q (f x)).

  Variables (Lq : _) (qe : list_enumerator Lq q).

  Variables (x0 : X).
  
  Variables (d : eq_dec Y).
  
  Local Fixpoint L L' n :=
    match n with
    | 0 => []
    | S n => L L' n ++ [ x | x ∈ cumul L' n , In (f x) (cumul Lq n) ]
    end.

  Lemma enum_red L' :
    list_enumerator__T L' X ->
    list_enumerator (L L') p.
  Proof.
    intros HL'.
    split.
    + intros H.
      eapply Hf in H. eapply (cumul_spec qe) in H as [m1]. destruct (cumul_spec__T HL' x) as [m2 ?]. 
      exists (1 + m1 + m2). cbn. in_app 2.
      in_collect x.
      eapply cum_ge'; eauto; try lia.
      eapply cum_ge'; eauto; try lia.
    + intros [m H]. induction m.
      * inversion H.
      * cbn in H. inv_collect. 
        eapply Hf. eauto.
  Qed.

End enum_red.

Lemma enumerable_red X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerable__T X -> discrete Y -> enumerable q -> enumerable p.
Proof.
  intros [f] [] % enum_enumT [] % discrete_iff [L] % enumerable_enum.
  eapply list_enumerable_enumerable.
  eexists. eapply enum_red; eauto.
Qed.

Theorem not_decidable X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerable__T X -> ~ enumerable (compl p) ->
  ~ decidable q /\ ~ decidable (compl q).
Proof.
  intros. split; intros ?.
  - eapply H1. eapply dec_red in H2; eauto.
    eapply dec_compl in H2. eapply dec_count_enum; eauto.
  - eapply H1. eapply dec_red in H2; eauto.
    eapply dec_count_enum; eauto. now eapply red_comp.
Qed.

Theorem not_coenumerable X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerable__T X -> ~ enumerable (compl p) -> discrete Y ->
  ~ enumerable (compl q).
Proof.
  intros. intros ?. eapply H1. eapply enumerable_red in H3; eauto.
  now eapply red_comp.
Qed.
