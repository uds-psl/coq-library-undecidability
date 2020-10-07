Require Import FunInd.

From Undecidability Require Import TM.Code.Copy.
From Undecidability Require Import TM.Code.CodeTM.
From Undecidability Require Import TM.Compound.Compare.
From Undecidability Require Import TM.Basic.Basic.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac TM.Compound.Multi.
From Undecidability Require Import TM.Lifting.LiftTapes.


Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


Lemma pair_inv (X Y : Type) (x1 x2 : X) (y1 y2 : Y) :
  (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2.
Proof. intros H. now inv H. Qed.



(** * Compare two values *)

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
      destruct (current t1); auto; destruct (current t2); auto.
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


  (** Worst-case time (read the full string) *)
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
    - simpl_list; cbn. rewrite Compare_correct_neq_midtape; cbn; auto. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_short_midtape; cbn; auto. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_long_midtape; cbn; auto. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
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
    - simpl_list; cbn. rewrite Compare_correct_neq_midtape; cbn; auto. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_short_midtape; cbn; auto. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
    - simpl_list; cbn. rewrite Compare_correct_long_midtape; cbn; auto. rewrite MoveToSymbol_L_steps_midtape; auto. simpl_list. lia.
  Qed.

End Compare_fun_lemmas.


Lemma app_cons_neq (X : Type) (xs ys1 ys2 : list X) (x y : X) :
  x <> y -> xs ++ x :: ys1 <> xs ++ y :: ys2.
Proof.
  revert ys1 ys2. induction xs as [ | x' xs' IH]; intros; cbn in *.
  - intros H'. inv H'. tauto.
  - intros H'. inv H'. eapply IH; eauto.
Qed.

Lemma list_length_neq (X : Type) (xs ys : list X) :
  length xs <> length ys -> xs <> ys.
Proof. now intros ? ->. Qed.


Section CompareValues.

  Variable sigX : finType.
  Variable (X : eqType) (cX : codable sigX X).

  Hypothesis cX_injective : forall x1 x2, cX x1 = cX x2 -> x1 = x2.

  Definition CompareValues_Rel : pRel sigX^+ bool 2 :=
    fun tin '(yout, tout) =>
      forall (x1 x2 : X) (sx sy : nat),
        tin[@Fin0] ≃(;sx) x1 ->
        tin[@Fin1] ≃(;sy) x2 ->
        (yout = if Dec (x1=x2) then true else false) /\
        tout[@Fin0] ≃(;sx) x1 /\
        tout[@Fin1] ≃(;sy) x2.
                     

  Definition CompareValues : pTM sigX^+ bool 2 :=
    Switch (Compare (@isStop sigX))
           (fun res => Return (LiftTapes (MoveToSymbol_L (@isStart sigX) id) [|Fin0|];; LiftTapes (MoveToSymbol_L (@isStart sigX) id) [|Fin1|]) res).


  Lemma CompareValues_Realise : CompareValues ⊨ CompareValues_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold CompareValues. apply Switch_Realise. apply Compare_Realise. intros res. TM_Correct. }
    {
      intros tin (yout, tout) H. intros x1 x2 sx sy HEncX1 HEncX2. TMSimp.
      hnf in HEncX1. destruct HEncX1 as (r1&HEncX1&Hsx). destruct HEncX2 as (r2&HEncX2&Hsy). TMSimp. 

      pose proof compare_lists (cX x1) (cX x2) as[ HC | [ (a&b&l1&l2&l3&HC1&HC2&HC3) | [ (a&l1&l2&HC1&HC2) | (a&l1&l2&HC1&HC2) ]]].
      { (* Case [x1=x2] *)
        apply cX_injective in HC as <-. decide (x1=x1) as [ _ | ?]; [ | tauto ].
        rewrite Compare_correct_eq_midtape in H; cbn; auto.
        - inv H; TMSimp. repeat split; auto.
          + hnf. rewrite MoveToSymbol_L_correct_midtape; cbn; auto.
            * eexists. f_equal. split.
              -- now rewrite map_id, rev_involutive.
              -- auto.
            * now intros ? (?&<-&?) % in_rev % in_map_iff.
          + hnf. rewrite MoveToSymbol_L_correct_midtape; cbn; auto.
            * eexists. split.
              -- f_equal. now rewrite map_id, rev_involutive.
              -- auto.
            * now intros ? (?&<-&?) % in_rev % in_map_iff.
        - now intros ? (?&<-&?) % in_map_iff.
      }
      { (* Case [x1] and x2 differ in char [a] and [b] *)
        decide (x1 = x2) as [ <- | ].
        { exfalso. eapply app_cons_neq with (xs := l1) (x := a) (y := b); eauto. rewrite <- HC2. eauto. }
        rewrite HC2, HC3 in H. rewrite !map_app, <- !app_assoc, !map_cons in H. cbn in H.
        rewrite Compare_correct_neq_midtape in H; cbn; auto.
        - inv H. repeat split; auto.
          + hnf. rewrite MoveToSymbol_L_correct_midtape; cbn; auto. eauto. rewrite map_id, rev_involutive, HC2.
            * eexists. split.
              -- f_equal. simpl_list. auto.
              -- auto.
            * now intros ? (?&<-&?) % in_rev % in_map_iff.
          + hnf. rewrite MoveToSymbol_L_correct_midtape; cbn; auto. eauto. rewrite map_id, rev_involutive, HC3.
            * eexists. split.
              -- f_equal. simpl_list. auto.
              -- auto.
            * now intros ? (?&<-&?) % in_rev % in_map_iff.
        - now intros ? (?&<-&?) % in_map_iff.
        - congruence.
      }
      { (* Case [x1] is longer [x2] *)
        decide (x1 = x2) as [ <- | ].
        { exfalso. eapply list_length_neq with (xs := l1 ++ a :: l2) (ys := l1); eauto. simpl_list; cbn; lia. congruence. }
        rewrite HC1, HC2 in H. rewrite !map_app, <- !app_assoc, !map_cons in H. cbn in H.
        rewrite Compare_correct_short_midtape in H; cbn; auto.
        - inv H. repeat split; auto.
          + hnf. rewrite MoveToSymbol_L_correct_midtape; cbn; auto. eauto. rewrite map_id, rev_involutive, HC1.
            * eexists. split.
              -- f_equal. simpl_list. auto.
              -- auto.
            * now intros ? (?&<-&?) % in_rev % in_map_iff.
          + hnf. rewrite MoveToSymbol_L_correct_midtape; cbn; auto. eauto. rewrite map_id, rev_involutive.
            * eexists. split.
              -- f_equal.
              -- auto.
            * now intros ? (?&<-&?) % in_rev % in_map_iff.
        - now intros ? (?&<-&?) % in_map_iff.
      }
      { (* Case [x1] is shorter [x2] *)
        decide (x1 = x2) as [ <- | ].
        { exfalso. eapply list_length_neq with (xs := l1 ++ a :: l2) (ys := l1); eauto. simpl_list; cbn; lia. congruence. }
        rewrite HC1, HC2 in H. rewrite !map_app, <- !app_assoc, !map_cons in H. cbn in H.
        rewrite Compare_correct_long_midtape in H; cbn; auto.
        - inv H. repeat split; auto.
          + hnf. rewrite MoveToSymbol_L_correct_midtape; cbn; auto. eauto. rewrite map_id, rev_involutive.
            * eexists. split.
              -- f_equal.
              -- auto.
            * now intros ? (?&<-&?) % in_rev % in_map_iff.
          + hnf. rewrite MoveToSymbol_L_correct_midtape; cbn; auto. eauto. rewrite map_id, rev_involutive, HC2.
            * eexists. split.
              -- f_equal. simpl_list. auto.
              -- auto.
            * now intros ? (?&<-&?) % in_rev % in_map_iff.
        - now intros ? (?&<-&?) % in_map_iff.
      }
    }
  Qed.


  (* 11 + 6 * max (size _ x1) (size _ x2) for Compare *)
  (* 8 + 4 * (size _ x1) for MoveToSymbol_L @ [|Fin0|] *)
  (* 8 + 4 * (size _ x2) for MoveToSymbol_L @ [|Fin1|] *)
  Definition CompareValues_steps {sigX X : Type} {cX : codable sigX X} (x1 x2 : X) :=
    29 + 6 * max (size _ x1) (size _ x2) + 4 * (size _ x1) + 4 * (size _ x2).

  Definition CompareValues_T : tRel sigX^+ 2 :=
    fun tin k => exists (x1 x2 : X), tin[@Fin0] ≃ x1 /\ tin[@Fin1] ≃ x2 /\ CompareValues_steps x1 x2 <= k.


  Lemma CompareValues_TerminatesIn : projT1 CompareValues ↓ CompareValues_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold CompareValues. TM_Correct.
      - apply Compare_Realise.
      - apply Compare_TerminatesIn. }
    {
      intros tin k (x1&x2&HEncX1&HEncX2&Hk). unfold CompareValues_steps in Hk. cbn.
      destruct HEncX1 as (r1&HEncX1). destruct HEncX2 as (r2&HEncX2). TMSimp.
      exists (11 + 6 * max (size _ x1) (size _ x2)), (17 + 4 * (size _ x1) + 4 * (size _ x2)). repeat split; try lia.
      { hnf. TMSimp. rewrite Compare_steps_correct_midtape; auto. simpl_list. reflexivity. }
      intros tmid ymid HCompare.
      rewrite surjective_pairing in HCompare. apply pair_inv in HCompare as [-> HCompare].
      rewrite surjective_pairing in HCompare. apply pair_inv in HCompare as [HCompare1 HCompare2].
      (* Both cases are actually the same *)
      match goal with [ |- (if ?H then _ else _) _ _ ] => destruct H end.
      {
        exists (8 + 4 * (size _ x1)), (8 + 4 * (size _ x2)). repeat split; try lia.
        { rewrite HCompare1. rewrite Compare_Move_steps_midtape1; cbn; auto.
          simpl_list; reflexivity. all: now intros ? (?&<-&?) % in_map_iff. }
        { intros tmid0 [] (HMove1&HMoveInj). TMSimp. rewrite Compare_Move_steps_midtape2; cbn; auto.
          simpl_list; reflexivity. all: now intros ? (?&<-&?) % in_map_iff. }
      }
      {
        exists (8 + 4 * (size _ x1)), (8 + 4 * (size _ x2)). repeat split; try lia.
        { rewrite HCompare1. rewrite Compare_Move_steps_midtape1; cbn; auto.
          simpl_list; reflexivity. all: now intros ? (?&<-&?) % in_map_iff. }
        { intros tmid0 [] (HMove1&HMoveInj). TMSimp. rewrite Compare_Move_steps_midtape2; cbn; auto.
          simpl_list; reflexivity. all: now intros ? (?&<-&?) % in_map_iff. }
      }
    }
  Qed.

End CompareValues.

Arguments CompareValues_steps {sigX X cX} : simpl never.
(* no size *)



(*
Section CompareValues_steps_comp.
  Variable (sig tau: finType) (X:eqType) (cX: codable sig X).
  Variable (I : Retract sig tau).

  Lemma CompareValues_steps_comp (x1 x2 : X):
    CompareValues_steps (Encode_map cX I) x1 x2 = CompareValues_steps cX x1 x2.
  Proof. unfold CompareValues_steps. now rewrite !Encode_map_hasSize. Qed.

End CompareValues_steps_comp.
*)
