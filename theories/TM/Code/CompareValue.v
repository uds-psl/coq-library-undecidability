From Coq Require Import FunInd.

From Undecidability Require Import TM.Code.Copy.
From Undecidability Require Import TM.Code.CodeTM.
From Undecidability Require Import TM.Compound.Compare.
From Undecidability Require Import TM.Basic.Basic.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac TM.Compound.Multi.
From Undecidability Require Import TM.Lifting.LiftTapes.


Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Set Default Proof Using "Type".

Lemma pair_inv (X Y : Type) (x1 x2 : X) (y1 y2 : Y) :
  (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2.
Proof. intros H. now inv H. Qed.



(** * Compare two values *)


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
  Proof using cX_injective.
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


  (* 11 + 6 * max (size x1) (size x2) for Compare *)
  (* 8 + 4 * (size x1) for MoveToSymbol_L @ [|Fin0|] *)
  (* 8 + 4 * (size x2) for MoveToSymbol_L @ [|Fin1|] *)
  Definition CompareValues_steps {sigX X : Type} {cX : codable sigX X} (x1 x2 : X) :=
    29 + 6 * max (size x1) (size x2) + 4 * (size x1) + 4 * (size x2).

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
      exists (11 + 6 * max (size x1) (size x2)), (17 + 4 * (size x1) + 4 * (size x2)). repeat split; try lia.
      { hnf. TMSimp. rewrite Compare_steps_correct_midtape; auto. simpl_list. reflexivity. }
      intros tmid ymid HCompare.
      rewrite surjective_pairing in HCompare. apply pair_inv in HCompare as [-> HCompare].
      rewrite surjective_pairing in HCompare. apply pair_inv in HCompare as [HCompare1 HCompare2].
      (* Both cases are actually the same *)
      match goal with [ |- (if ?H then _ else _) _ _ ] => destruct H end.
      {
        exists (8 + 4 * (size x1)), (8 + 4 * (size x2)). repeat split; try lia.
        { rewrite HCompare1. rewrite Compare_Move_steps_midtape1; cbn; auto.
          simpl_list; reflexivity. all: now intros ? (?&<-&?) % in_map_iff. }
        { intros tmid0 [] (HMove1&HMoveInj). TMSimp. rewrite Compare_Move_steps_midtape2; cbn; auto.
          simpl_list; reflexivity. all: now intros ? (?&<-&?) % in_map_iff. }
      }
      {
        exists (8 + 4 * (size x1)), (8 + 4 * (size x2)). repeat split; try lia.
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

From Undecidability Require Import HoareLogic HoareRegister HoareTactics.

Section CompareValues.

  Variable (sigX : finType) (X : eqType) (cX : codable sigX X).
  Hypothesis (HInj : forall x y, cX x = cX y -> x = y).

  Lemma CompareValue_SpecT_size (x y : X) (ss : Vector.t nat 2) :
    TripleT (≃≃(([], withSpace  [|Contains _ x; Contains _ y |] ss)))
            (CompareValues_steps x y) (CompareValues sigX)
            (fun yout => ≃≃([if yout then x=y else x<>y],withSpace [|Contains _ x; Contains _ y|] (appSize [|id; id|] ss))).
  Proof using HInj. unfold withSpace.
    eapply Realise_TripleT.
    - now apply CompareValues_Realise.
    - now apply CompareValues_TerminatesIn.
    - intros tin yout tout H HEnc. cbn in *. 
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. cbn in *. 
      cbn in *; simpl_vector in *; cbn in *.
      modpon H. rewrite H. tspec_solve. now decide _.
    - intros tin k HEnc Hk. cbn in *.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
      cbn in *; simpl_vector in *; cbn in *.
      unfold CompareValues_T. eauto.
  Qed.

  Lemma CompareValue_SpecT (x y : X) :
    TripleT (≃≃([], [|Contains _ x; Contains _ y|]))
            (CompareValues_steps x y) (CompareValues sigX)
            (fun yout => ≃≃([if yout then x=y else x<>y],[|Contains _ x; Contains _ y|])).
  Proof using HInj. eapply TripleT_RemoveSpace. cbn. intros s. apply CompareValue_SpecT_size. Qed.

  Lemma CompareValue_Spec_size (x y : X) (ss : Vector.t nat 2) :
    Triple (≃≃(([], withSpace  [|Contains _ x; Contains _ y |] ss)))
           (CompareValues sigX)
           (fun yout => ≃≃([if yout then x=y else x<>y],withSpace [|Contains _ x; Contains _ y|] (appSize [|id; id|] ss))).
  Proof using HInj. eapply TripleT_Triple. apply CompareValue_SpecT_size. Qed.

  Lemma CompareValue_Spec (x y : X) :
    Triple (≃≃([], [|Contains _ x; Contains _ y|]))
           (CompareValues sigX)
           (fun yout => ≃≃([if yout then x=y else x<>y],[|Contains _ x; Contains _ y|])).
  Proof using HInj. eapply Triple_RemoveSpace. apply CompareValue_Spec_size. Qed.

End CompareValues.
