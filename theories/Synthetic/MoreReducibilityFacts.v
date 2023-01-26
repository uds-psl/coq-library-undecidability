From Undecidability.Synthetic Require Import 
  ReducibilityFacts DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts MoreEnumerabilityFacts.

Require Import List.
Import ListNotations.
From Undecidability.Shared Require Import Dec.

#[local] Coercion dec2bool P (d: dec P) := if d then true else false.

Set Implicit Arguments.

Section enum_red.

  Variables (X Y : Type) (p : X -> Prop) (q : Y -> Prop).
  Variables (f : X -> Y) (Hf : forall x, p x <-> q (f x)).

  Variables (Lq : _) (qe : list_enumerator Lq q).

  Variables (x0 : X).
  
  Variables (d : eq_dec Y).
  
  Local Fixpoint L L' n :=
    match n with
    | 0 => []
    | S n => L L' n ++ (filter (fun x => Dec (In (f x) (cumul Lq n))) (cumul L' n))
    end.

  Local Lemma enum_red L' :
    list_enumerator__T L' X ->
    list_enumerator (L L') p.
  Proof using qe Hf.
    intros HL'.
    split.
    + intros H.
      eapply Hf in H. eapply (cumul_spec qe) in H as [m1]. destruct (cumul_spec__T HL' x) as [m2 ?]. 
      exists (1 + m1 + m2). cbn. apply in_app_iff. right.
      apply filter_In. split.
      * eapply cum_ge'; eauto; lia.
      * eapply Dec_auto. eapply cum_ge'; eauto; lia.
    + intros [m H]. induction m.
      * inversion H.
      * cbn in H. apply in_app_or in H. destruct H; [now auto|].
        apply filter_In in H. destruct H as [_ H].
        destruct (Dec _) in H; [|easy].
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

Lemma semi_decidable_red (X Y : Type) (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> semi_decidable q -> semi_decidable p.
Proof.
  intros [f Hf] [g Hg]. exists (fun x n => g (f x) n).
  firstorder.
Qed.

Theorem not_decidable X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerable__T X -> ~ enumerable (complement p) ->
  ~ decidable q /\ ~ decidable (complement q).
Proof.
  intros. split; intros ?.
  - eapply H1. eapply dec_red in H2; eauto.
    eapply dec_compl in H2. eapply dec_count_enum; eauto.
  - eapply H1. eapply dec_red in H2; eauto.
    eapply dec_count_enum; eauto. now eapply red_comp.
Qed.

Theorem not_coenumerable X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> enumerable__T X -> ~ enumerable (complement p) -> discrete Y ->
  ~ enumerable (complement q).
Proof.
  intros. intros ?. eapply H1. eapply enumerable_red in H3; eauto.
  now eapply red_comp.
Qed.
