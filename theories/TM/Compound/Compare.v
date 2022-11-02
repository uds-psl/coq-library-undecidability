Require Import FunInd.

From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Basic.Basic.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability.TM.Compound Require Import TMTac Multi MoveToSymbol.

Require Recdef.


(* * Compare two tapes (from left to right) until a symbol is reached *)

(* This two-tape machines reads symbols from the tapes. It moves right, until the read symbols are not equal, or one of the read symbol is a stop symbol. It returns [true] if both last read symbols are stop symbols. It returns [false] If one (or both) tapes finally are off the tape, or the last read symbols differ. *)

Section Compare.
  Import Recdef.

  Variable sig : finType.
  Variable stop : sig -> bool. (* stop symbol(s) *)


  Definition Compare_Step : pTM sig (option bool) 2 :=
    Switch
      (CaseChar2 (fun c1 c2 =>
                    match c1, c2 with
                    | Some c1, Some c2 =>
                      if (stop c1) && (stop c2)
                      then Some true (* both stop symbols were reached at the same time ~> strings are equal *)
                      else if (stop c1) || (stop c2)
                           then Some false (* Only one stop symbol was reached ~> one string is longer *)
                           else if Dec (c1 = c2)
                                then None (* up to here, the strings are the same *)
                                else Some false (* symbols differ! *)
                    | _, _ => Some false (* At least one string not terminated *)
                    end))
      (fun x : option bool => match x with
                        | Some b => Return Nop (Some b)
                        | None => Return (MovePar Rmove Rmove) None
                        end).


  Definition Compare_Step_Rel : pRel sig (option bool) 2 :=
    fun tin '(yout, tout) =>
      match current tin[@Fin0], current tin[@Fin1] with
      | Some c1, Some c2 =>
        if (stop c1) && (stop c2)
        then yout = Some true /\ tout = tin
        else if (stop c1) || (stop c2)
             then yout = Some false /\ tout = tin
             else if Dec (c1 = c2)
                  then yout = None /\ tout[@Fin0] = tape_move_right tin[@Fin0] /\ tout[@Fin1] = tape_move_right tin[@Fin1]
                  else yout = Some false /\ tout = tin
      | _, _ => yout = Some false /\ tout = tin
      end.


  Lemma Compare_Step_Sem : Compare_Step ⊨c(5) Compare_Step_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Compare_Step. TM_Correct. }
    { Unshelve. 4,7: reflexivity. all: lia. }
    { intros tin (yout, tout) H. TMCrush; TMSolve 1. }
  Qed.


  Definition Compare := While Compare_Step.


  Definition Compare_fun_measure (t : tape sig * tape sig) : nat := length (tape_local (fst t)).

  Function Compare_fun (t : tape sig * tape sig) {measure Compare_fun_measure t} : bool * (tape sig * tape sig) :=
    match (current (fst t)), (current (snd t)) with
    | Some c1, Some c2 =>
        if (stop c1) && (stop c2)
        then (true, t)
        else if (stop c1) || (stop c2)
             then (false, t)
             else if Dec (c1 = c2)
                  then Compare_fun (tape_move_right (fst t), tape_move_right (snd t))
                  else (false, t)
    | _, _ => (false, t)
    end.
  Proof.
    intros (t1&t2). intros c1 Hc1 c2 Hc2 HStopC1 HStopC2. cbn in *. 
    destruct t1; cbn in *; inv Hc1. destruct t2; cbn in *; inv Hc2.
    unfold Compare_fun_measure. cbn. simpl_tape. intros. lia.
  Qed.


  Definition Compare_Rel : pRel sig bool 2 :=
    fun tin '(yout, tout) => (yout, (tout[@Fin0], tout[@Fin1])) = Compare_fun (tin[@Fin0], tin[@Fin1]).

  Lemma Compare_Realise : Compare ⊨ Compare_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Compare. TM_Correct. eapply RealiseIn_Realise. apply Compare_Step_Sem. }
    { apply WhileInduction; intros; cbn in *.
      - revert yout HLastStep. TMCrush; intros; rewrite Compare_fun_equation; cbn; TMSolve 1.
        all:try rewrite E in *; try rewrite E0 in *;try rewrite E1 in *;try rewrite E2 in *. 
        all: TMCrush; TMSolve 1.  
      - revert yout HLastStep. TMCrush; intros. all:TMSimp. all:rewrite HLastStep.
        all:symmetry. all:rewrite Compare_fun_equation. all:cbn. all:rewrite E, E0, E1, E2. all:decide (e0=e0) as [ | Tamtam]; [ | now contradiction Tamtam] . all:auto.
    }
  Qed.


  Local Arguments plus : simpl never.

  Function Compare_steps (t : tape sig * tape sig) { measure Compare_fun_measure} : nat :=
    match (current (fst t)), (current (snd t)) with
    | Some c1, Some c2 =>
        if (stop c1) && (stop c2)
        then 5
        else if (stop c1) || (stop c2)
             then 5
             else if Dec (c1 = c2)
                  then 6 + Compare_steps (tape_move_right (fst t), tape_move_right (snd t))
                  else 5
    | _, _ => 5
    end.
  Proof.
    intros (t1&t2). intros c1 Hc1 c2 Hc2 HStopC1 HStopC2. cbn in *. 
    destruct t1; cbn in *; inv Hc1. destruct t2; cbn in *; inv Hc2.
    unfold Compare_fun_measure. cbn. simpl_tape. intros. lia.
  Qed.


  Definition Compare_T : tRel sig 2 :=
    fun tin k => Compare_steps (tin[@Fin0], tin[@Fin1]) <= k.


  Lemma Compare_steps_ge t : 5 <= Compare_steps t.
  Proof. functional induction Compare_steps t; auto. lia. Qed.
    

  Lemma Compare_TerminatesIn : projT1 Compare ↓ Compare_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Compare. TM_Correct.
      - eapply RealiseIn_Realise. apply Compare_Step_Sem.
      - eapply RealiseIn_TerminatesIn. apply Compare_Step_Sem. }
    { apply WhileCoInduction; intros. exists 5. split. reflexivity. intros [ yout | ].
      - intros. hnf in HT. TMCrush. all: rewrite <- HT. all: apply Compare_steps_ge.
      - intros. hnf in HT. exists (Compare_steps (tape_move tin[@Fin0] Rmove, tape_move tin[@Fin1] Rmove)).
        TMCrush.
        split.
        + hnf. TMSimp. auto.
        + rewrite Compare_steps_equation in HT. cbn in HT. rewrite E, E0, E1, E2 in HT. rewrite E3 in *. lia.
    }
  Qed.
    

End Compare.


Section CompareLists.

  Variable X : eqType.
  
  Definition list_comperasion (xs ys : list X) : Prop :=
    xs = ys \/
    (exists a b l1 l2 l3, a <> b /\ xs = l1 ++ a :: l2 /\ ys = l1 ++ b :: l3) \/
    (exists a l1 l2, xs = l1 ++ a :: l2 /\ ys = l1) \/
    (exists a l1 l2, xs = l1 /\ ys = l1 ++ a :: l2).

  Definition list_comperasion_cons xs ys x :
    list_comperasion xs ys ->
    list_comperasion (x :: xs) (x :: ys).
  Proof.
    destruct 1 as [ <- | [ (a&b&l1&l2&l3&H1&H2&H3) | [ (a&l1&l2&H1&H2) | (a&l1&l2&H1&H2) ]]].
    - left. reflexivity.
    - subst. right; left. exists a, b, (x::l1), l2, l3. auto.
    - subst. right. right. left. do 3 eexists. split. 2: reflexivity. cbn. eauto.
    - subst. right. right. right. do 3 eexists. split. 1: reflexivity. cbn. eauto.
  Qed.

  Lemma compare_lists (xs ys : list X) :
    list_comperasion xs ys.
  Proof.
    revert ys. induction xs as [ | x xs IH]; intros; cbn in *.
    - destruct ys as [ | y ys].
      + left. reflexivity.
      + right. right. right. do 3 eexists. split. reflexivity. cbn. reflexivity.
    - destruct ys as [ | y ys].
      + hnf. right. right. left. do 3 eexists. split. 2: reflexivity. cbn. reflexivity.
      + decide (x = y) as [ <- | HDec].
        * now apply list_comperasion_cons.
        * hnf. right. left. exists x, y, nil. cbn. do 2 eexists. eauto.
  Qed.

End CompareLists.


Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Section Compare_fun_lemmas.

  Variable (X : finType) (stop : X -> bool).


  Lemma Compare_correct_eq (str : list X) (s1 s2 : X) rs1 rs2 t :
    (forall x, In x str -> stop x = false) ->
    stop s1 = true ->
    stop s2 = true ->
    tape_local (fst t) = str ++ s1 :: rs1 ->
    tape_local (snd t) = str ++ s2 :: rs2 ->
    Compare_fun stop t =
    (true, (midtape (rev str ++ left (fst t)) s1 rs1, midtape (rev str ++ left (snd t)) s2 rs2)).
  Proof.
    revert str s1 s2 rs1 rs2. functional induction (Compare_fun stop t); intros str s1 s2 rs1 rs2 HStr HS1 HS2 HL1 HL2; destruct t as [t1 t2]; cbn in *;
                                try rewrite HS1 in *; try rewrite HS2 in *; cbn in *; auto.
    - destruct str as [ | s str']; cbn in *.
      + apply midtape_tape_local_cons in HL1 as ->. apply midtape_tape_local_cons in HL2 as ->. cbn. reflexivity.
      + apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2.
        rewrite HL1 in *. cbn in *. inv e. rewrite HL2 in *. cbn in *. inv e0.
        specialize (HStr c2 ltac:(auto)). rewrite HStr in e1. cbn in *. congruence.
    - (* absurd case *) exfalso. destruct str as [ | s str']; cbn in *.
      + apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2. rewrite HL1, HL2 in *. cbn in *. inv e; inv e0. rewrite HS1, HS2 in e1. cbn in *. congruence.
      + apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2. rewrite HL1, HL2 in *. cbn in *. inv e; inv e0.
        specialize (HStr c2 ltac:(auto)). rewrite HStr in *. cbn in *. congruence.
    - (* Induction case *) destruct str as [ | s str']; cbn in *.
      + exfalso. apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2. rewrite HL1, HL2 in *. cbn in *. inv e; inv e0. rewrite HS1 in e1. cbn in *. congruence.
      + apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2. rewrite HL1, HL2 in *. cbn in *. inv e; inv e0.
        apply orb_false_iff in e2 as (e2&_).
        simpl_tape in IHp. specialize IHp with (4 := eq_refl) (5 := eq_refl) (2 := HS1) (3 := HS2). spec_assert IHp by auto.
        simpl_list; cbn; auto.
    - (* absurd case *) exfalso. destruct str as [ | s str']; cbn in *.
      + apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2. rewrite HL1, HL2 in *. cbn in *. inv e; inv e0. rewrite HS1, HS2 in e1. cbn in *. congruence.
      + apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2. rewrite HL1, HL2 in *. cbn in *. inv e; inv e0.
        specialize (HStr c2 ltac:(auto)). rewrite HStr in *. cbn in *. congruence.
    - (* absurd case *) exfalso. destruct str as [ | s str']; cbn in *.
      + apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2. rewrite HL1, HL2 in *. cbn in *. auto.
      + apply midtape_tape_local_cons in HL1. apply midtape_tape_local_cons in HL2. rewrite HL1, HL2 in *. cbn in *. auto.
  Qed.

  Lemma Compare_correct_eq_midtape (str : list X) (s1 s2 : X) ls1 rs1 ls2 m rs2 :
    (forall x, In x str -> stop x = false) ->
    stop m = false ->
    stop s1 = true ->
    stop s2 = true ->
    Compare_fun stop (midtape ls1 m (str ++ s1 :: rs1), midtape ls2 m (str ++ s2 :: rs2)) =
    (true, (midtape (rev str ++ m :: ls1) s1 rs1, midtape (rev str ++ m :: ls2) s2 rs2)).
  Proof.
    intros HStr Hm HS1 HS2.
    rewrite Compare_fun_equation; cbn. erewrite Compare_correct_eq with (str := str) (rs1 := rs1) (rs2 := rs2) (s1 := s1) (s2 := s2); eauto.
    all: cbn; simpl_tape; auto.
    rewrite Hm. cbn. decide (m=m); [ | tauto]. now simpl_tape.
  Qed.


  Lemma Compare_correct_neq (str1 str2 str3 : list X) (x1 x2 : X) t :
    (forall x, In x str1 -> stop x = false) ->
    stop x1 = false ->
    stop x2 = false ->
    x1 <> x2 ->
    tape_local (fst t) = str1 ++ x1 :: str2 ->
    tape_local (snd t) = str1 ++ x2 :: str3 ->
    Compare_fun stop t =
    (false, (midtape (rev str1 ++ left (fst t)) x1 str2, midtape (rev str1 ++ left (snd t)) x2 str3)).
  Proof.
    revert str1 str2 str3 x1 x2. functional induction (Compare_fun stop t); intros str1 str2 str3 x1 x2; intros Hstr1 Hx1 Hx2 Hx12 HT1 HT2; destruct t as [t1 t2]; cbn in *.
    - exfalso. destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0. rewrite Hx1 in e1. cbn in *. congruence.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. specialize (Hstr1 s ltac:(eauto)). inv e; inv e0.
        rewrite Hstr1 in e1. cbn in *. congruence.
    - exfalso. destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0. rewrite Hx1 in e2. cbn in *. congruence.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. specialize (Hstr1 s ltac:(eauto)).
        inv e; inv e0. rewrite Hstr1 in e2. cbn in *. congruence.
    - (* inductive case *) destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0. tauto.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0.
        simpl_tape in IHp. specialize IHp with (5 := eq_refl) (6 := eq_refl) (2 := Hx1) (3 := Hx2) (4 := Hx12). spec_assert IHp by auto.
        simpl_list; cbn; auto.
    - destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0. rewrite Hx1 in e2. cbn in *. congruence.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0. now contradiction _x.
    - exfalso. destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. auto.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. auto.
  Qed.

  Lemma Compare_correct_neq_midtape (str1 str2 str3 : list X) (m x1 x2 : X) ls1 ls2 :
    (forall x, In x str1 -> stop x = false) ->
    stop x1 = false ->
    stop x2 = false ->
    stop m = false ->
    x1 <> x2 ->
    Compare_fun stop (midtape ls1 m (str1 ++ x1 :: str2), midtape ls2 m (str1 ++ x2 :: str3)) =
    (false, (midtape (rev str1 ++ m :: ls1) x1 str2, midtape (rev str1 ++ m :: ls2) x2 str3)).
  Proof.
    intros Hstr1 Hx1 Hx2 Hm Hx12.
    rewrite Compare_fun_equation; cbn. rewrite Compare_correct_neq with (str1 := str1) (str2 := str2) (str3 := str3) (x1 := x1) (x2 := x2).
    all: cbn; simpl_tape; auto.
    rewrite Hm. cbn. decide (m=m); [ | tauto]. now simpl_tape.
  Qed.


  Definition swap (A B : Type) : A*B->B*A := ltac:(intros [b a]; now constructor).

  Lemma Compare_correct_swap t :
    Compare_fun stop (swap t) = (fst (Compare_fun stop t), swap (snd (Compare_fun stop t))).
  Proof.
    functional induction (Compare_fun stop t); destruct t as [t1 t2]; cbn in *.
    - rewrite Compare_fun_equation. cbn. rewrite e, e0.
      rewrite andb_comm in e1. now rewrite e1.
    - rewrite Compare_fun_equation. cbn. rewrite e, e0.
      rewrite andb_comm in e1. rewrite orb_comm in e2. now rewrite e1, e2.
    - rewrite Compare_fun_equation. cbn. rewrite e, e0.
      rewrite e1, e2. decide (c1=c1) as [ ? | H]; [ | now contradiction H]. auto.
    - rewrite Compare_fun_equation. cbn. rewrite e, e0.
      rewrite andb_comm in e1. rewrite orb_comm in e2. rewrite e1, e2.
      decide (c2=c1) as [ <- | H]; [ now contradiction _x | ]. auto.
    - rewrite Compare_fun_equation. cbn.
      destruct (current t1); auto; destruct (current t2); easy.
  Qed.


  Lemma Compare_correct_short (str1 str2 rs1 rs2 : list X) (x : X) (s1 s2 : X) t :
    (forall x, In x str1 -> stop x = false) ->
    stop x = false ->
    stop s1 = true ->
    stop s2 = true ->
    tape_local (fst t) = str1 ++ x :: str2 ++ s1 :: rs1 ->
    tape_local (snd t) = str1 ++ s2 :: rs2 ->
    Compare_fun stop t =
    (false, (midtape (rev str1 ++ left (fst t)) x (str2 ++ s1 :: rs1),
             midtape (rev str1 ++ left (snd t)) s2 rs2)).
  Proof.
    revert str1 str2 rs1 rs2 x s1 s2. functional induction (Compare_fun stop t); intros str1 str2 rs1 rs2 x s1 s2; intros Hstr1 Hx Hs1 Hs2 HT1 HT2; destruct t as [t1 t2]; cbn in *.
    - exfalso. destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0. rewrite Hx in e1. cbn in e1. congruence.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0.
        specialize (Hstr1 c2 ltac:(auto)). rewrite Hstr1 in e1. cbn in e1. congruence.
    - destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. auto.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0.
        specialize (Hstr1 c2 ltac:(auto)). rewrite Hstr1 in e2. cbn in e2. congruence.
    - (* induction case *) destruct str1 as [ | s str1]; cbn in *.
      + exfalso. apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0.
        rewrite Hs2 in e1. cbn in e1. congruence.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0.
        simpl_tape in IHp. specialize IHp with (2 := Hx) (3 := Hs1) (4 := Hs2) (5 := eq_refl) (6 := eq_refl). spec_assert IHp by auto.
        simpl_list; cbn; auto.
    - exfalso. destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0. rewrite Hx in e2. cbn in e2. congruence.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. inv e; inv e0.
        specialize (Hstr1 c2 ltac:(auto)). rewrite Hstr1 in e1. cbn in e1. congruence.
    - exfalso. destruct str1 as [ | s str1]; cbn in *.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. auto.
      + apply midtape_tape_local_cons in HT1. apply midtape_tape_local_cons in HT2. rewrite HT1, HT2 in *. cbn in *. auto.
  Qed.


  Lemma Compare_correct_short_midtape (str1 str2 : list X) (x s1 s2 : X) ls1 rs1 ls2 m rs2 :
    (forall x, In x str1 -> stop x = false) ->
    stop m = false ->
    stop x = false ->
    stop s1 = true ->
    stop s2 = true ->
    Compare_fun stop (midtape ls1 m (str1 ++ x :: str2 ++ s1 :: rs1),
                      midtape ls2 m (str1 ++ s2 :: rs2)) =
    (false, (midtape (rev str1 ++ m :: ls1) x (str2 ++ s1 :: rs1),
             midtape (rev str1 ++ m :: ls2) s2 rs2)).
  Proof.
    intros Hstr1 Hm Hx Hs1 Hs2.
    erewrite Compare_correct_short with (str1 := m :: str1) (str2 := str2) (s1 := s1) (s2 := s2); cbn; eauto.
    - now simpl_list; cbn.
    - intros ? [ <- | H]; auto.
  Qed.


  Lemma Compare_correct_long_midtape (str1 str2 : list X) (x s1 s2 : X) ls1 rs1 ls2 m rs2 :
    (forall x, In x str1 -> stop x = false) ->
    stop m = false ->
    stop x = false ->
    stop s1 = true ->
    stop s2 = true ->
    Compare_fun stop (midtape ls2 m (str1 ++ s2 :: rs2),
                      midtape ls1 m (str1 ++ x :: str2 ++ s1 :: rs1)) =
    (false, (midtape (rev str1 ++ m :: ls2) s2 rs2,
             midtape (rev str1 ++ m :: ls1) x (str2 ++ s1 :: rs1))).
  Proof.
    change ((midtape ls2 m (str1 ++ s2 :: rs2), midtape ls1 m (str1 ++ x :: str2 ++ s1 :: rs1))) with (swap (midtape ls1 m (str1 ++ x :: str2 ++ s1 :: rs1), midtape ls2 m (str1 ++ s2 :: rs2))).
    change (midtape (rev str1 ++ m :: ls2) s2 rs2, midtape (rev str1 ++ m :: ls1) x (str2 ++ s1 :: rs1)) with (swap (midtape (rev str1 ++ m :: ls1) x (str2 ++ s1 :: rs1), midtape (rev str1 ++ m :: ls2) s2 rs2)).
    intros. rewrite Compare_correct_swap. cbn. rewrite Compare_correct_short_midtape; eauto.
  Qed.


  (* Worst-case time (read the full string) *)
  Lemma Compare_steps_correct (str1 str2 : list X) (s1 s2 : X) rs1 rs2 t :
    stop s1 = true ->
    stop s2 = true ->
    tape_local (fst t) = str1 ++ s1 :: rs1 ->
    tape_local (snd t) = str2 ++ s2 :: rs2 ->
    Compare_steps stop t <= 5 + 6 * max (length str1) (length str2).
  Proof.
    revert rs1 rs2 str1 str2. functional induction (Compare_steps stop t); intros rs1 rs2 str1 str2; intros Hs1 Hs2 HT1 HT2; destruct t as [t1 t2]; cbn in *.
    all: try lia. (* this solves all but the inductive case *)
    destruct str1 as [ | s str1], str2 as [ | s' str2]; cbn in *;
      apply midtape_tape_local_cons in HT1; apply midtape_tape_local_cons in HT2; rewrite HT1, HT2 in *; cbn in *;
        inv e; inv e0.
    - exfalso. rewrite Hs1 in e1. cbn in e1. congruence.
    - exfalso. rewrite Hs1 in e1. cbn in e1. congruence.
    - exfalso. rewrite Hs2 in e2. cbn in e2. congruence.
    - simpl_tape in IHn. specialize IHn with (1 := Hs1) (2 := Hs2) (3 := eq_refl) (4 := eq_refl). lia.
  Qed.

  Lemma Compare_steps_correct_midtape (str1 str2 : list X) (s1 s2 : X) (m : X) ls1 ls2 rs1 rs2 :
    stop s1 = true ->
    stop s2 = true ->
    Compare_steps stop (midtape ls1 m (str1 ++ s1 :: rs1), midtape ls2 m (str2 ++ s2 :: rs2)) <= 11 + 6 * max (length str1) (length str2).
  Proof.
    intros Hs1 Hs2. rewrite Compare_steps_correct with (str1 := m :: str1) (str2 := m :: str2) (s1 := s1) (s2 := s2); cbn; eauto. lia.
  Qed.

  (* Worst case steps for moving back after comparing *)
  Lemma Compare_Move_steps_midtape1 (stop' : X -> bool) (str1 str2 : list X) (s1 s2 : X) (m : X) ls1 ls2 rs1 rs2 :
    (forall x, In x str1 -> stop x = false) ->
    (forall x, In x str2 -> stop x = false) ->
    stop m = false ->
    stop s1 = true ->
    stop s2 = true ->
    stop' m = true ->
    (forall x, In x str1 -> stop' x = false) ->
    (forall x, In x str2 -> stop' x = false) ->
    MoveToSymbol_L_steps stop' id (fst (snd (Compare_fun stop (midtape ls1 m (str1 ++ s1 :: rs1), midtape ls2 m (str2 ++ s2 :: rs2))))) <=
    8 + 4 * length str1.
  Proof.
    intros.
    pose proof compare_lists str1 str2 as[ HC | [ (a&b&l1&l2&l3&HC1&HC2&HC3) | [ (a&l1&l2&HC1&HC2) | (a&l1&l2&HC1&HC2) ]]]; subst.
    - rewrite Compare_correct_eq_midtape; cbn; auto. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_neq_midtape; cbn; auto with list. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_short_midtape; cbn; auto with list. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_long_midtape; cbn; auto with list. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
  Qed.

  Lemma Compare_Move_steps_midtape2 (stop' : X -> bool) (str1 str2 : list X) (s1 s2 : X) (m : X) ls1 ls2 rs1 rs2 :
    (forall x, In x str1 -> stop x = false) ->
    (forall x, In x str2 -> stop x = false) ->
    stop m = false ->
    stop s1 = true ->
    stop s2 = true ->
    stop' m = true ->
    (forall x, In x str1 -> stop' x = false) ->
    (forall x, In x str2 -> stop' x = false) ->
    MoveToSymbol_L_steps stop' id (snd (snd (Compare_fun stop (midtape ls1 m (str1 ++ s1 :: rs1), midtape ls2 m (str2 ++ s2 :: rs2))))) <=
    8 + 4 * length str2.
  Proof.
    intros.
    pose proof compare_lists str1 str2 as[ HC | [ (a&b&l1&l2&l3&HC1&HC2&HC3) | [ (a&l1&l2&HC1&HC2) | (a&l1&l2&HC1&HC2) ]]]; subst.
    - rewrite Compare_correct_eq_midtape; cbn; auto. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_neq_midtape; cbn; auto with list. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_short_midtape; cbn; auto with list. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_long_midtape; cbn; auto with list. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
  Qed.

End Compare_fun_lemmas.