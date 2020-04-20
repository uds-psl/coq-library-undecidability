From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations.

Lemma enumerable_enum {X} {p : X -> Prop} :
  enumerable p <-> list_enumerable p.
Proof.
  split. eapply enumerable_list_enumerable. eapply list_enumerable_enumerable.
Qed.

Lemma enumerable_disj X (p q : X -> Prop) :
  enumerable p -> enumerable q -> enumerable (fun x => p x \/ q x).
Proof.
  intros [Lp H] % enumerable_enum [Lq H0] % enumerable_enum.
  eapply enumerable_enum.
  exists (fix f n := match n with 0 => [] | S n => f n ++ [ x | x ∈ Lp n] ++ [ y | y ∈ Lq n] end).
  intros x. split.
  - intros [H1 | H1].
    * eapply H in H1 as [m]. exists (1 + m). cbn. in_app 2. in_collect x. eauto.
    * eapply H0 in H1 as [m]. exists (1 + m). cbn. in_app 3. in_collect x. eauto.
  - intros [m]. induction m.
    * inversion H1.
    * inv_collect;
      unfold list_enumerator in *; firstorder.
Qed.

Lemma enumerable_conj X (p q : X -> Prop) :
  discrete X -> enumerable p -> enumerable q -> enumerable (fun x => p x /\ q x).
Proof.
  intros [] % discrete_iff [Lp] % enumerable_enum [Lq] % enumerable_enum.
  eapply enumerable_enum.
  exists (fix f n := match n with 0 => [] | S n => f n ++ [ x | x ∈ cumul Lp n, In x (cumul Lq n)] end).
  intros x. split.
  + intros []. eapply (list_enumerator_to_cumul H) in H1 as [m1].
    eapply (list_enumerator_to_cumul H0) in H2 as [m2].
    exists (1 + m1 + m2). cbn. in_app 2.
    in_collect x.
    eapply cum_ge'. eauto. eauto. lia.
    eapply cum_ge'; eauto. lia.
  + intros [m]. induction m.
    * inversion H1.
    * inv_collect. eapply (list_enumerator_to_cumul H). eauto.
      eapply (list_enumerator_to_cumul H0). eauto.
Qed.

Lemma projection X Y (p : X * Y -> Prop) :
  enumerable p -> enumerable (fun x => exists y, p (x,y)).
Proof.
  intros [f].
  exists (fun n => match f n with Some (x, y) => Some x | None => None end).
  intros; split.
  - intros [y ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
  - intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inversion H0; subst.
    exists y. eapply H. eauto.
Qed.

Lemma projection' X Y (p : X * Y -> Prop) :
  enumerable p -> enumerable (fun y => exists x, p (x,y)).
Proof.
  intros [f].
  exists (fun n => match f n with Some (x, y) => Some y | None => None end).
  intros y; split.
  - intros [x ?]. eapply H in H0 as [n]. exists n. now rewrite H0.
  - intros [n ?]. destruct (f n) as [ [] | ] eqn:E; inversion H0; subst.
    exists x. eapply H. eauto.
Qed.
