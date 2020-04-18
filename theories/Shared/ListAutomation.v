Require Export List Undecidability.Shared.Dec Undecidability.Shared.FilterFacts.

Local Notation "x 'el' L" := (In x L) (at level 80).

Instance list_in_dec X (x : X) (A : list X) :
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Qed.

Lemma in_concat_iff A l (a:A) : a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
  induction l; cbn.
  - intuition. now destruct H. 
  - rewrite in_app_iff, IHl. clear. firstorder subst. auto.
Qed.

Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).

Notation "[ s | p ∈ A ',' P ]" :=
  (map (fun p => s) (filter (fun p => Dec P) A)) (p pattern).
Notation "[ s | p ∈ A ]" :=
  (map (fun p => s) A) (p pattern).

Ltac in_app n :=
  (match goal with
  | [ |- In _ (_ ++ _) ] => 
    match n with
    | 0 => idtac
    | 1 => eapply in_app_iff; left
    | S ?n => eapply in_app_iff; right; in_app n
    end
  | [ |- In _ (_ :: _) ] => match n with 0 => idtac | 1 => left | S ?n => right; in_app n end
  end) || (repeat (try right; eapply in_app_iff; right)).

Lemma to_dec (P : Prop) `{dec P} : P <-> is_true (Dec P).
Proof.
  split; destruct (Dec P); cbn in *; firstorder congruence.
Qed.

Ltac in_collect a :=
  eapply in_map_iff; exists a; split; [ eauto | match goal with [ |- In _ (filter _ _) ] =>  eapply in_filter_iff; split; [ try (rewrite !in_prod_iff; repeat split) | eapply Dec_auto; repeat split; eauto ] | _ => try (rewrite !in_prod_iff; repeat split) end ].
Ltac inv_collect :=
  repeat
    (match goal with
    | [ H : ?x el concat _ |- _ ] => eapply in_concat_iff in H as (? & ? & ?)
    | [ H : ?x el map _ _ |- _ ] => let x := fresh "x" in eapply in_map_iff in H as (x & ? & ?)
    | [ x : ?A * ?B |- _ ] => destruct x; subst
    | [ H : ?x el filter _ _ |- _ ] => let H' := fresh "H" in eapply in_filter_iff in H as (? & H' % to_dec)
    | [ H : ?x el list_prod _ _ |- _ ] => eapply in_prod_iff in H
    | [ H : _ el _ ++ _ |- _ ] => try eapply in_app_iff in H as []
    | [H : _ el _ :: _ |- _ ] => destruct H
     end; intuition; subst).
