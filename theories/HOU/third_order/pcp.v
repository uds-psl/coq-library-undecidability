Set Implicit Arguments.
Require Import List.
From Undecidability.HOU Require Import std.std. 
Import ListNotations.

(** * PCP and MPCP *)
Notation symbol := bool.
Notation word   := (list symbol).
Notation card   := (word * word)%type.
Notation stack  := (list card).

Notation hd := fst.
Notation tl := snd. 
Notation heads S := (map hd S).
Notation tails S := (map tl S).




Definition PCP (S: list card) :=
  exists (I: list nat),  I ⊆ nats (|S|) /\ I <> nil /\ 
                  concat (select I (heads S)) = concat (select I (tails S)).

Definition MPCP '(c, C) :=
  exists (I: list nat), I ⊆ nats (1 + |C|)
                 /\ hd c ++ @concat symbol (select I (heads (c :: C))) = tl c ++ concat (select I (tails (c :: C))).


Definition PCPsimp (C: list card) :=
  exists (C': stack),  C' ⊆ C /\ C' <> nil /\ concat (heads C') = concat (tails C').

Definition MPCPsimp '(c, C) :=
  exists (C': stack), C' ⊆ c :: C  /\ hd c ++ concat (heads C') = tl c ++ concat (tails C').





(* ** Equivalences *)
Section PCPEquivalence.

  Hint Resolve nth_error_Some_lt nth_error_lt_Some nats_lt lt_nats : core.


  Lemma incl_select_iff X (A B: list X):
    A ⊆ B <-> exists I, I ⊆ nats (length B) /\ select I B = A.
  Proof.
    split.
    - now intros ? % incl_select.
    - intros [I [? <-]]; eapply select_incl. 
  Qed.


  Lemma PCPsimp_PCP C:
    PCPsimp C <-> PCP C.
  Proof.
    split. 
    + intros [C' H]. rewrite incl_select_iff in H.
      destruct H as ((I & ? & ?) & ? & ?); subst.
      exists I. rewrite <-!select_map; intuition.
      subst; cbn in *; intuition. 
    + intros (I & H).  exists (select I C). rewrite incl_select_iff.
      intuition eauto.
      destruct I; intuition. cbn in H1. specialize (H0 n); mp H0; lauto.
      eapply nats_lt, nth_error_lt_Some in H0 as [? ?].
      rewrite H0 in H1; discriminate.
      rewrite !select_map; intuition.
  Qed.


  Lemma MPCPsimp_MPCP c C:
    MPCPsimp (c,C) <-> MPCP (c,C).
  Proof.
    split. 
    + intros [C' H]. rewrite incl_select_iff in H.
      destruct H as ((I & ? & ?) & ?); subst.
      exists I. rewrite <-!select_map; intuition.
    + intros (I & H).  exists (select I (c :: C)). rewrite incl_select_iff.
      intuition eauto. rewrite !select_map; intuition.
  Qed.


End PCPEquivalence.



