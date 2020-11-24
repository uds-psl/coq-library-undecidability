From Undecidability.Shared.Libs.PSL Require Import Lists.Cardinality Numbers.

(* ** Finite inductive predicates *)

Section Fip.
  Variables (X: eqType) (sigma: list X -> X -> bool) (R: list X).
  
  Inductive fip : X -> Prop :=
  | fip_intro A x : (forall x, x el A -> fip x) -> sigma A x -> x el R -> fip x.

  Definition fip_monotone := forall A B x, A <<= B -> sigma A x -> sigma B x.
  Definition fip_closed A := forall x, x el R -> sigma A x -> x el A.

  Lemma fip_least A x :
    fip_monotone -> fip_closed A -> fip x -> x el A.
  Proof.
    intros C D. induction 1 as [B x _ IH F G].
    apply (D _ G). revert F. apply C. exact IH.
  Qed.

  Fixpoint fip_it n A : list X :=
    match n, find (fun x => Dec (~ x el A /\ sigma A x)) R with
    | S n', Some x => fip_it n' (x::A)
    | _, _ =>  A
    end.

  Lemma fip_it_sound n A :
    inclp A fip -> inclp (fip_it n A) fip.
  Proof.
    revert A; induction n as [|n IH]; cbn; intros A H.
    - exact H.
    - destruct (find _ R) as[x|] eqn:E.
      (* New: Remember equation, apply find specs to it, elim Dec _ = true *)
      + apply find_some in E as [H1 (H2&H3) % Dec_true].
        apply IH. intros z [<-|H4].
        * apply fip_intro with (A:= A); auto.
        * apply H, H4.
      + apply H.
  Qed.

  Lemma fip_it_closed n A :
    A <<= R -> card R <= n + card A -> fip_closed (fip_it n A).
  Proof.
    revert A. induction n as [|n IH]; cbn; intros A H H1.
    - enough (A === R) as (H2&H3) by (hnf; auto).
      apply card_or in H as [H|H]. exact H. lia.
    - destruct (find _ R) eqn:E.
      + apply find_some in E as [H2 (H3&H4) % Dec_true]. apply IH. now auto. 
        rewrite card_cons'. lia. auto.
      + intros x H2 H3. apply dec_DN. now auto.
        apply find_none with (x := x) in E; auto.
        apply Dec_false in E; auto. 
  Qed.

  Theorem fip_dec x :
    fip_monotone -> dec (fip x).
  Proof.
    intros D.
    apply dec_transfer with (P:= x el fip_it (card R) nil); [ | now auto].
    split.
    - revert x. apply fip_it_sound. hnf. auto.
    - apply (fip_least D). apply fip_it_closed. now auto. lia.
  Qed.

End Fip.

(* ** Finite closure iteration *)

Module FCI.
Section FCI.
  Variables (X: eqType) (sigma: list X -> X -> bool) (R: list X).

  Lemma pick (A : list X) :
    { x | x el R /\ sigma A x /\ ~ x el A } + { forall x, x el R -> sigma A x -> x el A }.
  Proof.
    destruct (cfind R (fun x => sigma A x /\ ~ x el A)) as [E|E].
    - auto.
    - right. intros x F G.
      decide (x el A). assumption. exfalso.
      eapply E; eauto.
  Qed.

  Definition F (A : list X) : list X.
    destruct (pick A) as [[x _]|_].
    - exact (x::A).
    - exact A.
  Defined.

  Definition C := it F (card R) nil.
  
  Lemma it_incl n : 
    it F n nil <<= R.
  Proof.
    apply it_ind. now auto.
    intros A E. unfold F. 
    destruct (pick A) as [[x G]|G]; intuition.
  Qed.
  
  Lemma incl :
    C <<= R.
  Proof.
    apply it_incl.
  Qed.

  Lemma ind p :
    (forall A x, inclp A p -> x el R -> sigma A x -> p x) -> inclp C p.
  Proof.
    intros B. unfold C. apply it_ind.
    + intros x [].
    + intros D G x. unfold F.
      destruct (pick D) as [[y E]|E].
      * intros [[]|]; intuition; eauto.
      * intuition.
  Qed.

  Lemma fp : 
    F C = C.
  Proof.
    pose (size (A : list X) := card R - card A).
    replace C with (it F (size nil) nil).
    - apply it_fp. intros n. cbn. 
      set (J:= it F n nil). unfold FP, F.
      destruct (pick J) as [[x B]|B].
      + right.
        assert (G: card J < card (x :: J)).
        { apply card_lt with (x:=x); intuition. }
        assert (H: card (x :: J) <= card R).
        { apply card_le, incl_cons. apply B. apply it_incl. }
        unfold size. lia.
      + auto.
    - unfold C, size. f_equal. change (card nil) with 0. lia.
  Qed.
  
  Lemma closure x :
    x el R -> sigma C x -> x el C.
  Proof.
    assert (A2:= fp).
    unfold F in A2.
    destruct (pick C) as [[y C]| B].
    + contradiction (list_cycle A2). 
    + apply B.
  Qed.

  Theorem fip_dec x :  (* Proof using FCI *)
    fip_monotone sigma -> dec (fip sigma R x).
  Proof.
    intros D.
    apply dec_transfer with (P:= x el C). 2:now auto.
    split.
    - revert x. apply FCI.ind. intros A x IH E F.
      apply fip_intro with (A:=A); auto.
    - apply (fip_least D). intros z. apply FCI.closure.
  Qed.

End FCI.
End FCI.

(* Print Graph. (* prints transitive closure of coercions *) *)
