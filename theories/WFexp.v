Set Implicit Arguments.
Require Import List Coq.Sorting.Permutation Morphisms.

Notation "A == B" := (Permutation A B) (at level 70).

Definition perm (X : Type) (R : list X -> list X -> Prop) A B :=
  exists A', A == A' /\ R A' B.

(** Automatically turn a :: A into (a :: nil) ++ A if A ≠ nil *)
Ltac appify :=
  match goal with
  | [ |- context[?a :: ?A] ] =>
    lazymatch A with
    | nil => fail
    | _ => change (a :: A) with ((a :: nil) ++ A); appify
    end
  | [ H : context[?a :: ?A] |- _ ] =>
    lazymatch A with
    | nil => fail
    | _ => change (a :: A) with ((a :: nil) ++ A) in H; appify
    end
  | _ => idtac
  end.

(** Tactics to ease solving goals involving permutations arising in SDialogues.v **)

Ltac rewrite_app t A B :=
  lazymatch B with
  | _ :: ?B' => rewrite_app t A B'
  | A ++ t :: ?B' => rewrite <- (@Permutation_cons_app _ (A ++ B') A B' t); [|reflexivity]
  | _ ++ ?B' => rewrite_app t A B'
  end.

(** Pull the term t to the front of the sublist A of the left-hand side of the claim **)
Ltac perml t A :=
  lazymatch A with
  | t :: ?A' => idtac
  | ?b :: ?A' => perml t A'; rewrite (perm_swap t b)
  | ?B ++ ?A' => perml t A'; match goal with |- ?L == _ => rewrite_app t B L end
  end.

(** Pull the term t to the front of the sublist A of the right-hand side of the claim.

    This tactic relies on rewrites and should thus be applied only after perml has been
    applied for the same term to guarantee that the rewrite actually take place at the
    intended position.
 **)
Ltac permr t A :=
  lazymatch A with
  | t :: ?A' => idtac
  | ?b :: ?A' => permr t A'; rewrite (perm_swap t b)
  | ?B ++ ?A' => permr t A'; match goal with |- _ == ?R => rewrite_app t B R end
  end.

Ltac permp' t :=
  lazymatch goal with |- ?L == _ => perml t L end;
  lazymatch goal with |- _ == ?R => permr t R end;
  apply perm_skip.

Ltac permp'' L n :=
  lazymatch n with
  | O => lazymatch L with ?t :: _ => permp' t end
  | S ?n' =>
    lazymatch L with
    | _ :: ?L' => permp'' L' n'
    | _ ++ ?L' => permp'' L' n'
    end
  end.

(** Eliminate the value at the n-th position of the left-hand side of the claim from both lists **)
Ltac permp n :=
  lazymatch goal with |- ?L == _ => permp'' L n end.

(** **** Well-foundedness of well-behaved list relations **)
Section WFlist.
  Variable X : Type.
  Variable R : list X -> list X -> Prop.
  Hypothesis R_app : forall A B C, R C (A ++ B) -> (exists A', R A' A /\ C = A' ++ B) \/ (exists B', R B' B /\ C = A ++ B').
  Hypothesis R_app_l : forall A A' B, R A' A -> R (A' ++ B) (A ++ B).
  Hypothesis R_app_r : forall A B B', R B' B -> R (A ++ B') (A ++ B).

  Lemma Acc_app A B :
    Acc R A -> Acc R B -> Acc R (A ++ B).
  Proof.
    induction 1 as [A HA IHA] in B |-*; induction 1 as [B HB IHB].
    constructor. intros ? [(A' & HA' & ->) | (B' & HB' &  ->)] % R_app.
    - apply IHA. 2: constructor. all: easy.
    - now apply IHB.
  Qed.

  Lemma well_founded_singleton_full :
    (forall x, Acc R (x :: nil)) -> Acc R nil -> well_founded R.
  Proof.
    intros Hsing Hbase A. induction A.
    - apply Hbase.
    - appify. now apply Acc_app.
  Qed.

  Lemma Acc_app_rev A B :
    Acc R (A ++ B) -> Acc R A /\ Acc R B.
  Proof.
    enough (forall C, Acc R C -> forall A B, C = A ++ B -> Acc R A /\ Acc R B) by (intros; now apply (H (A ++ B))).
    clear A B. intros C. induction 1 as [? HC IHC]. intros A B ->. split.
    - constructor. intros A' HR % (R_app_l B). now destruct (IHC _ HR A' B).
    - constructor. intros B' HR % (R_app_r A). now destruct (IHC _ HR A B').
  Qed.

  Lemma Permutation_cons_split a (A B : list X) :
    a :: A == B -> exists B1 B2, B = B1 ++ a :: B2 /\ A == B1 ++ B2.
  Proof.
    enough (forall A B, A == B -> forall C C' c, A = C ++ c :: C' -> exists B1 B2, B = B1 ++ c :: B2 /\ C ++ C' == B1 ++ B2)
    by (intros; now apply (H (a :: A) B H0 nil A a)).
    clear a A B. intros A B; intros perm; induction perm.
    - intros [] ? ?; inversion 1.
    - intros [] C' c; cbn.
      + intros [= -> ->]. now exists nil, l'.
      + intros [= -> ->]. destruct (IHperm l0 C' c eq_refl) as (B1 & B2 & -> & HB).
        exists (x0 :: B1), B2; cbn. split. easy. auto.
    - intros [| c1 [| c2 C]] C' c; cbn.
      + destruct C' as [| c2 C']. 1: inversion 1. intros [= -> -> ->]. now exists (c2 :: nil), C'.
      + intros [= -> -> ->]. now exists nil, (c1 :: C').
      + intros [= -> -> ->]. exists (c2 :: c1 :: C), C'; cbn; split. easy. apply perm_swap.
    - intros C C' c ->. destruct (IHperm1 C C' c eq_refl) as (B & B' & -> & HB).
      destruct (IHperm2 B B' c eq_refl) as (D & D' & -> & HC).
      exists D, D'; split. easy. now transitivity (B ++ B').
  Qed.

  Lemma perm_R A B B' :
    R A B -> B == B' -> exists A', A == A' /\ R A' B'.
  Proof.
    induction B in A, B' |-*; intros HR.
    - intros -> % Permutation_nil. now exists A.
    - intros (C1 & C2 & -> & HC) % Permutation_cons_split. appify.
      destruct (R_app (a :: nil) B HR) as [(A' & ? & HA') | (C' & ? & HC')]; subst.
      + exists (C1 ++ A' ++ C2). split. 2: now apply R_app_r, R_app_l.
        rewrite app_assoc, (Permutation_app_comm C1 A'), <- app_assoc.
        now apply Permutation_app_head.
      + destruct (IHB C' (C1 ++ C2) H HC) as (D & HD & HD').
        destruct (R_app C1 C2 HD') as [(C1' & ? & HC1') | (C2' & ? & HC2')]; subst.
        * exists (C1' ++ (a :: nil) ++ C2). split. 2: now apply R_app_l.
          rewrite app_assoc, (Permutation_app_comm C1' (a :: nil)), <- app_assoc.
          now apply Permutation_app_head.
        * exists (C1 ++ (a :: nil) ++ C2'). split. 2: now apply R_app_r, R_app_r.
          rewrite app_assoc, (Permutation_app_comm C1 (a :: nil)), <- app_assoc.
          now apply Permutation_app_head.
  Qed.

  Lemma Acc_perm A B :
    Acc R A -> A == B -> Acc R B.
  Proof.
    induction A in B |-*.
    - now intros ? -> % Permutation_nil.
    - appify. intros ? % Acc_app_rev (C & C' & -> & ? % IHA % Acc_app_rev) % Permutation_cons_split.
      appify. repeat apply Acc_app. all: intuition.
  Qed.

  Lemma Acc_perm' A B :
    Acc R A -> A == B -> Acc (perm R) B.
  Proof.
    induction 1 as [A HA IHA] in B |-*. constructor. intros C (C' & H1 & H2).
    symmetry in H. destruct (perm_R H2 H) as (B' & HB' & RB').
    apply (IHA _ RB' C). symmetry. now transitivity C'.
  Qed.

  Lemma well_founded_perm :
    well_founded R -> well_founded (perm R).
  Proof.
    intros Hwf A. now apply (Acc_perm' (Hwf A)).
  Qed.
End WFlist.

Lemma Acc_iff (X : Type) (R R' : X -> X -> Prop) :
  (forall x y, R x y <-> R' x y) -> well_founded R -> well_founded R'.
Proof.
  intros HR wf_R x. induction (wf_R x). constructor. intros y H' % HR. now apply H0.
Qed.

(** **** The exponential step relation **)

Section WFexp.
  Variable X : Type.
  Variable R : X -> X -> Prop.
  Hypothesis wf_R : well_founded R.

  Definition lexp B A :=
    exists A1 A2 Y x, A = A1 ++ x :: A2 /\ Forall (fun y => R y x) Y /\ B == A1 ++ Y ++ A2.

  Definition lexp' B A :=
    exists A1 A2 Y x, A = A1 ++ x :: A2 /\ Forall (fun y => R y x) Y /\ B = A1 ++ Y ++ A2.

  Lemma lexp_perm_lexp' B A :
    perm lexp' B A <-> lexp B A.
  Proof.
    split.
    - intros (B' & HB' & A1 & A2 & Y & x & HA & HY & HB). subst. now exists A1, A2, Y, x.
    - intros (A1 & A2 & Y & x & HA & HY & HB). exists (A1 ++ Y ++ A2). firstorder. now exists A1, A2, Y, x.
  Qed.

  Lemma app_split_two (A B C D : list X) x :
    A ++ B = C ++ x :: D ->
    (exists A1 A2, A = A1 ++ x :: A2 /\ C = A1 /\ D = A2 ++ B) \/
    (exists B1 B2, B = B1 ++ x :: B2 /\ C = A ++ B1 /\ D = B2).
  Proof.
    induction A in C |-*; cbn.
    - intros ->. right. now exists C, D.
    - destruct C; cbn; inversion 1; subst.
      + left. now exists nil, A.
      + destruct (IHA _ H2) as [(A1 & A2 & -> & -> & ->) | (B1 & B2 & -> & -> & ->)];
          [left; now exists (x0 :: A1), A2 | right; now exists B1, B2].
  Qed.

  Lemma lexp'_app A B C :
    lexp' C (A ++ B) -> (exists A', lexp' A' A /\ C = A' ++ B) \/ (exists B', lexp' B' B /\ C = A ++ B' ).
  Proof.
    intros (C1 & C2 & Y & x & [(A1 & A2 & ? & ? & ?) | (B1 & B2 & ? & ? & ?)] % app_split_two & HY & ?); subst.
    - left. exists (A1 ++ Y ++ A2). split. 2: now rewrite! app_assoc. now exists A1, A2, Y, x.
    - right. exists (B1 ++ Y ++ B2). split. 2: now rewrite! app_assoc. now exists B1, B2, Y, x.
  Qed.

  Lemma lexp'_nil :
    Acc lexp' nil.
  Proof.
    constructor. intros A ([] & A2 & Y & ? & H & ? & ?); inversion H.
  Qed.

  Lemma lexp'_single x :
    Acc lexp' (x :: nil).
  Proof.
    induction (wf_R x). constructor. intros ? (A & B & Y & x' & H1 & HY & ->).
    assert (A = nil) as ->; cbn in *. { destruct A. reflexivity. destruct A; cbn in *; inversion H1. }
    assert (B = nil) as ->; cbn in *. { destruct B. reflexivity. inversion H1. } inversion H1; subst.
    rewrite app_nil_r. induction Y. 1: apply lexp'_nil. inversion HY; subst. appify. apply (Acc_app lexp'_app).
    1: now apply H0. now apply IHY.
  Qed.

  Lemma lexp'_app_l A A' B :
    lexp' A' A -> lexp' (A' ++ B) (A ++ B).
  Proof.
    intros (A1 & A2 & Y & x & -> & HY & ->). repeat rewrite <- app_assoc. now exists A1, (A2 ++ B), Y, x.
  Qed.

  Lemma lexp'_app_r A B B' :
    lexp' B' B -> lexp' (A ++ B') (A ++ B).
  Proof.
    intros (B1 & B2 & Y & x & -> & HY & ->). rewrite! (app_assoc A B1). now exists (A ++ B1), (B2), Y, x.
  Qed.

  Lemma well_founded_lexp :
    well_founded lexp.
  Proof.
    eapply Acc_iff. apply lexp_perm_lexp'. apply (well_founded_perm lexp'_app lexp'_app_l lexp'_app_r).
    apply (well_founded_singleton_full lexp'_app lexp'_single lexp'_nil).
  Qed.
End WFexp.

(** **** Well-foundedness under transitive closure **)

Section Transitivity.
  Variable X : Type.
  Variable R : X -> X -> Prop.
  Hypothesis wf_R : well_founded R.

  Inductive trans (x : X) : X -> Prop :=
  | tone y : R x y -> trans x y
  | ttwo y z : R x y -> trans y z -> trans x z.

  Global Instance trans_Transitive : Transitive trans.
  Proof. intros x y z H H'. induction H; eauto using trans. Qed.

  Lemma well_founded_trans :
    well_founded trans.
  Proof.
    intros x. induction (wf_R x). constructor. intros y. remember x. induction 1; subst.
    2: destruct (IHtrans eq_refl H H0). all: eauto using trans.
  Qed.
End Transitivity.

Section TransWFexp.
  Variable X : Type.
  Variable R : X -> X -> Prop.
  Hypothesis wf_R : well_founded R.

  Definition tlexp := trans (lexp R).

  Lemma well_founded_tlexp :
    well_founded tlexp.
  Proof.
    now apply well_founded_trans, well_founded_lexp.
  Qed.
End TransWFexp.
