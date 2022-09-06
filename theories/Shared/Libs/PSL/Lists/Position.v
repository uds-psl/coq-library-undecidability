From Undecidability.Shared.Libs.PSL Require Export BaseLists Dupfree.
Require Import Arith.

Definition elAt := nth_error.
Notation "A '.[' i  ']'" := (elAt A i) (no associativity, at level 50).

Section Fix_X.

  Variable X : eqType.
  
  Fixpoint pos (s : X) (A : list X) :=
    match A with
    | nil => None
    | a :: A => if Dec (s = a) then Some 0 else match pos s A with None => None | Some n => Some (S n) end
    end.
  
  Lemma el_pos s A : s el A -> exists m, pos s A = Some m.
  Proof.
    revert s; induction A; simpl; intros s H.
    - contradiction.
    - decide (s = a) as [D | D]; eauto; 
        destruct H; try congruence.
      destruct (IHA s H) as [n Hn]; eexists; now rewrite Hn.
  Qed.
  
  Lemma pos_elAt s A i : pos s A = Some i -> A .[i] = Some s.
  Proof.
    revert i s. induction A; intros i s.
    - destruct i; inversion 1.
    - simpl. decide (s = a).
      + inversion 1; subst; reflexivity.
      + destruct i; destruct (pos s A) eqn:B; inversion 1; subst; eauto. 
  Qed.
  
  Lemma elAt_app (A : list X) i B s : A .[i] = Some s -> (A ++ B).[i] = Some s.
  Proof.
    revert s B i. induction A; intros s B i H; destruct i; simpl; intuition; inv H.
  Qed.
  
  Lemma elAt_el  A (s : X) m : A .[ m ] = Some s -> s el A.
  Proof.
    revert A. induction m; intros []; inversion 1; eauto.
  Qed.
  
  Lemma el_elAt (s : X) A : s el A -> exists m, A .[ m ] = Some s.
  Proof.
    intros H; destruct (el_pos H);  eexists; eauto using pos_elAt.
  Qed.

  Lemma dupfree_elAt (A : list X) n m s : dupfree A -> A.[n] = Some s -> A.[m] = Some s -> n = m.
  Proof with try tauto.
    intros H; revert n m; induction A; simpl; intros n m H1 H2.
    - destruct n; inv H1.
    - destruct n, m; inv H...
      + inv H1. simpl in H2. eapply elAt_el in H2...
      + inv H2. simpl in H1. eapply elAt_el in H1... 
      + inv H1. inv H2. rewrite IHA with n m... 
  Qed.

  Lemma nth_error_none A n l : nth_error l n = @None A -> length l <= n.
  Proof. revert n;
           induction l; intros n.
         - simpl; lia.
         - simpl. intros. destruct n. inv H. inv H. assert (| l | <= n). eauto. lia.
  Qed.

  Lemma pos_None (x : X) l l' : pos x l = None-> pos x l' = None -> pos x (l ++ l') = None.
  Proof.
    revert x l'; induction l; simpl; intros; eauto.
    have (x = a).
    destruct (pos x l) eqn:E; try congruence.
    rewrite IHl; eauto.
  Qed.

  Lemma pos_first_S (x : X)  l l' i  : pos x l = Some i -> pos x (l ++ l') = Some i.
  Proof.
    revert x i; induction l; intros; simpl in *.
    - inv H.
    - decide (x = a); eauto.
      destruct (pos x l) eqn:E.
      + eapply IHl in E. now rewrite E.
      + inv H.
  Qed.

  Lemma pos_second_S x l l' i : pos x l = None ->
                                pos x l' = Some i ->
                                pos x (l ++ l') = Some ( i + |l| ).
  Proof.
    revert i l'; induction l; simpl; intros.
    - rewrite Nat.add_comm. eauto.
    - destruct _; subst; try congruence.
      destruct (pos x l) eqn:EE. congruence.
      erewrite IHl; eauto.
  Qed.

  Lemma pos_length (e : X) n E : pos e E = Some n -> n < |E|.
  Proof.
    revert e n; induction E; simpl; intros.
    - inv H.
    - decide (e = a).
      + inv H. simpl. lia.
      + destruct (pos e E) eqn:EE.
        * inv H. assert (n1 < |E|) by eauto.  lia.
        * inv H.
  Qed.

  Fixpoint replace (xs : list X) (y y' : X) :=
    match xs with
    | nil => nil
    | x :: xs' => (if Dec (x = y) then y' else x) :: replace xs' y y'
    end.

  Lemma replace_same xs x : replace xs x x = xs.
  Proof.
    revert x; induction xs; intros; simpl; [ | destruct _; subst ]; congruence.
  Qed.

  Lemma replace_diff xs x y : x <> y -> ~ x el replace xs x y.
  Proof.
    revert x y; induction xs; intros; simpl; try destruct _; firstorder. 
  Qed.

  Lemma replace_pos xs x y y' : x <> y -> x <> y' -> pos x xs = pos x (replace xs y y').
  Proof.
    induction xs; intros; simpl.
    - reflexivity.
    - repeat destruct Dec; try congruence; try lia; subst. 
      + rewrite IHxs; eauto. + rewrite IHxs; eauto.
  Qed.

End Fix_X.

Arguments replace {_} _ _ _.



(* Fixpoint  getPosition {E: eqType} (A: list E) x := match A with *)
(*                                                    | nil => 0 *)
(*                                                    | cons x' A' => if Dec (x=x') then 0 else 1 + getPosition A' x end. *)

(* Lemma getPosition_correct {E: eqType} (x:E) A: if Dec (x el A) then forall z, (nth (getPosition A x) A z) = x else getPosition A x = |A |. *)
(* Proof. *)
(*   induction A;cbn. *)
(*   -dec;tauto. *)
(*   -dec;intuition; congruence. *)
(* Qed. *)
