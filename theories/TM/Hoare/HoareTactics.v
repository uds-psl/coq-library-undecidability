(* ** Very Convienient Verification Tactics for Hoare Logic *)

From Undecidability Require Import TMTac.
From Undecidability Require Import TM.Hoare.HoareLogic TM.Hoare.HoareCombinators TM.Hoare.HoareRegister TM.Hoare.HoareTacticsView.
From smpl Require Import Smpl.

(* We define tactics to "execute" the machine step-by-step during the verification. It uses [smpl] to be user-extensible. *)



(* Checks whether the given term contains an evar *)
Ltac contains_evar e := has_evar e.

(* Check if the goal triple is with space *)
Ltac triple_with_space :=
  lazymatch goal with
  | [ |- context [withSpace] ] => idtac
  end.



(* *** Smpl setup *)

(* For user extensions, like in [TM_Correct] *)
Smpl Create hstep_Spec.
Ltac hstep_Spec := smpl hstep_Spec.


(* *** Combinators *)

(* There is no tactic for While. *)


Ltac hstep_Seq :=
  match goal with
  | [ |- Triple ?P (?M1;; ?M2) ?Q ] => eapply Seq_Spec
  | [ |- TripleT ?P ?k (?M1;; ?M2) ?Q ] => eapply Seq_SpecT
  end.

(* Note: We often want to specify the running times ([k2] and [k3]) of [M2] and [M3] manually. For that, the user has to apply [If_SpecT] manually. *)
(* If desired, the user can apply the weak version [If_SpecT_weak] or [If_SpecT_weak'] manually. *)
Ltac hstep_If :=
  cbn beta;
  lazymatch goal with
  | [ |- Triple _ (If ?M1 ?M2 ?M3) _ ] => eapply If_Spec
  | [ |- TripleT ≃≃( _,_) ?k (If ?M1 ?M2 ?M3) _ ] =>
    eapply If_SpecTReg with (R:= fun y => (_,_)) (Q:= fun y => (_,_))
  | [ |- TripleT ?P ?k (If ?M1 ?M2 ?M3) ?Q ] => eapply If_SpecT
  end.

Ltac hstep_Switch :=
  lazymatch goal with
  | [ |- Triple ?P (Switch ?M1 ?M2) ?Q ] => eapply Switch_Spec
  | [ |- TripleT ?P ?k (Switch ?M1 ?M2) ?Q ] => eapply Switch_SpecT
  end.


(* For [Return], we may have to use the rule [Return_Spec_con]. *)
Ltac hstep_Return :=
  lazymatch goal with
  | [ |- Triple ?P (Return ?M ?x) ?Q ] =>
    (*tryif contains_evar Q then (eapply Return_Spec)
    else*) (eapply Return_Spec_con)
  | [ |- TripleT ?P ?k (Return ?M ?x) ?Q ] =>
    (*tryif contains_evar Q then (eapply Return_SpecT)
    else*) (eapply Return_SpecT_con)

  | [ |- Triple ?P (Relabel ?M ?f) ?Q ] =>
    (*tryif contains_evar Q then (eapply Relabel_Spec)
    else*) (eapply Relabel_Spec_con)
  | [ |- TripleT ?P ?k (Relabel ?M ?f) ?Q ] =>
    (* tryif contains_evar Q then (eapply Relabel_SpecT)
    else *) (eapply Relabel_SpecT_con)
  end.



(* ** Lifts *)

(* The rules for the lifts have been implemented for register machines only *)
(* We have special rules for specifications with space; and we also have to check whether the post-condition already is instantiated. *)
Ltac hstep_LiftTapes :=
  lazymatch goal with
  | [ |- Triple ?PRE (LiftTapes ?M ?I) ?POST ] =>
    tryif contains_evar POST then (* The post-condition is yet to be instantiated. *)
      (tryif triple_with_space
        then (eapply LiftTapes_Spec_space with (Q':= fun y => _) (Q:= fun y => _); [smpl_dupfree | ])
        else (eapply LiftTapes_Spec with (Q':= fun y => _) (Q:= fun y => _); [smpl_dupfree | ]))
    else (* Otherwise, we have to use the Consequence rule *)
      (tryif triple_with_space then (eapply LiftTapes_Spec_space_con with (R':= fun y => _) (R:= fun y => _); [smpl_dupfree | | ])
        else (eapply LiftTapes_Spec_con with (R':= fun y => _) (R:= fun y => _); [smpl_dupfree | | ]))
  | [ |- TripleT ?PRE ?k (LiftTapes ?M ?I) ?POST ] =>
    tryif contains_evar POST then
      (tryif triple_with_space then (refine (LiftTapes_SpecT_space (Q':= fun y => _) (Q:= fun y => _) _ _); [smpl_dupfree | ])
        else (refine (LiftTapes_SpecT (Q':= fun y => _) (Q:= fun y => _) _ _); [smpl_dupfree | ]))
    else
      (tryif triple_with_space then (eapply LiftTapes_SpecT_space_con with (R':= fun y => _) (R:= fun y => _); [smpl_dupfree | | ])
        else (eapply LiftTapes_SpecT_con with (R':= fun y => _) (R:= fun y => _); [smpl_dupfree | | ]))
  end.


(* [ChangeAlphabet] is similar to [LiftTapes], but we always have to apply at least [Consequence_pre]. We also have specialised rules for space. *)
Ltac hstep_ChangeAlphabet :=
  lazymatch goal with
  | [ |- Triple ?PRE (ChangeAlphabet ?M ?I)?POST ] =>
    tryif contains_evar POST then (* The post-condition is yet to be instantiated. *)
      (tryif triple_with_space then (eapply ChangeAlphabet_Spec_space_pre with (Q:= fun y => _) (Q0:= fun y => _); [ | ])
        else (eapply ChangeAlphabet_Spec_pre with (Q:= fun y => _) (Q0:= fun y => _); [ | ]))
    else (* Otherwise, we have to use the Consequence rule *)
      (tryif triple_with_space then (eapply ChangeAlphabet_Spec_space_pre_post  with (Q':= fun y => _) (Q0:= fun y => _); [ | | ])
        else (eapply ChangeAlphabet_Spec_pre_post with (Q':= fun y => _) (Q':= fun y => _) (Q0:= fun y => _); [ | | ]))
  | [ |- TripleT ?PRE ?k (ChangeAlphabet ?M ?I)?POST ] =>
    tryif contains_evar POST then
      (tryif triple_with_space then (eapply ChangeAlphabet_SpecT_space_pre with (Q:= fun y => _) (Q0:= fun y => _); [ | ])
        else (eapply ChangeAlphabet_SpecT_pre with (Q:= fun y => _) (Q0:= fun y => _); [ | ]))
    else
      (tryif triple_with_space then (eapply ChangeAlphabet_SpecT_space_pre_post with (Q':= fun y => _) (Q0:= fun y => _); [ | | ])
        else (eapply ChangeAlphabet_SpecT_pre_post with (Q:= fun y => _) (Q':= fun y => _) (Q0:= fun y => _); [ | | ]))
  end.

(*
Ltac hstep_ChangeAlphabet :=
  lazymatch goal with
  | [ |- Triple ?P (ChangeAlphabet ?M ?I)?Q ] =>
    tryif contains_evar Q then (eapply ChangeAlphabet_Spec)
    else (eapply ChangeAlphabet_Spec_con; [ | ])
  | [ |- TripleT ?P ?k (ChangeAlphabet ?M ?I)?Q ] =>
    tryif contains_evar Q then (eapply ChangeAlphabet_SpecT)
    else (eapply ChangeAlphabet_SpecT_pre_post; [ | ])
  end.
*)


(*
(* After applying lifts, we have to push [withSpace] to the front of the premise again. *)
Ltac hstep_withSpace_swap :=
  lazymatch goal with
  (* Rule for the tapes lift *)
  | [ |- Triple  (tspec (Frame (withSpace ?P ?ss) ?I (withSpace ?P' ?ss')))    ?M ?Q ] => eapply Triple_Frame_withSpace;  [now smpl_dupfree | ]
  | [ |- TripleT (tspec (Frame (withSpace ?P ?ss) ?I (withSpace ?P' ?ss'))) ?k ?M ?Q ] => eapply TripleT_Frame_withSpace; [now smpl_dupfree | ]

  | [ |- Triple  (tspec (Downlift (withSpace ?P ?ss) ?I))    ?M ?Q ] => eapply Triple_Downlift_withSpace
  | [ |- TripleT (tspec (Downlift (withSpace ?P ?ss) ?I)) ?k ?M ?Q ] => eapply TripleT_Downlift_withSpace

  (* Rules for the alphabet lift *)
  | [ |- Triple  (tspec (LiftSpec ?I (withSpace ?P ?ss)))    ?M ?Q ] => eapply Triple_LiftSpec_withSpace
  | [ |- TripleT (tspec (LiftSpec ?I (withSpace ?P ?ss))) ?k ?M ?Q ] => eapply TripleT_LiftSpec_withSpace
  end.
*)


(* *** Custom machines *)

(* We have to be careful with [Nop] and custom machines, because usually the postcondition is already instantiated. *)

(* The user only needs to specify the Termination rule. If the user wants to prove partial correctness, it it first checked whether
there is a corresponding Termination lemma. The tactic also takes care of whether we first have to apply the consequence rule. *)


(* make sure we don't try a space-rule if we don't know we want to use a space rule and see no precondition *)
Local Tactic Notation "noSpace" tactic(t) :=
  let test :=
  tryif triple_with_space
   then fail
    else reflexivity
  in
  lazymatch goal with
  | [ |- Triple ?P ?M ?Q ] =>
  eapply Consequence_pre;[t| test ]
  | [ |- TripleT ?P _ ?M ?Q ] => 
  eapply ConsequenceT_pre;[t| test |reflexivity]
  end || fail "could not find user-rule applicable here".


Ltac hstep_user :=
  lazymatch goal with
  | [ |- Triple ?P ?M ?Q ] => (* Without time *)
    tryif contains_evar Q then
      (tryif triple_with_space then
          (* Without time, but with space *)
          ((eapply TripleT_Triple; hstep_Spec) (* Weaken a registered rule with time and space *)
           || (hstep_Spec))
        else ((eapply TripleT_Triple;refine (TripleT_RemoveSpace (Q:=fun y => _) (Q':=fun y => _) _); now (intros; hstep_Spec)) (* Weaken a registered rule with time and space *)
              || (refine (TripleT_RemoveSpace (Q:=fun y => _) (Q':=fun y => _) _); now (intros; hstep_Spec)) (* Weaken a registered rule without time but with space *)
              || (eapply TripleT_Triple; hstep_Spec) (* Weaken a registered rule with time but without space *)
              || (noSpace hstep_Spec))) (* A registered rule without time and without space *)
    else (eapply Consequence_post; [ hstep_user | ]) (* First apply the consequence rule, then try again *)
  | [ |- TripleT ?P ?k ?M ?Q ] => (* With time *)
    tryif contains_evar Q then
      (tryif triple_with_space then hstep_Spec (* Apply the rule with time and space *)
        else (refine (TripleT_RemoveSpace (Q:=fun y => _) (Q':=fun y => _)_); now (intros; hstep_Spec)) (* Weaken a rule with time and space *)
             || (noSpace hstep_Spec))
    else (eapply ConsequenceT_post; [ hstep_user | ]) (* First apply the consequence rule, then try again *)
  end.

(* Example: [Nop] *)

Ltac hstep_Nop :=
  lazymatch goal with
  (* | [ |- Triple ?P Nop ?Q ] => eapply Nop_Spec *)
  | [ |- TripleT ?P ?k Nop ?Q ] => eapply Nop_SpecT
  end.

Smpl Add hstep_Nop : hstep_Spec.


(* *** Verification step tactic *)

(* Removes [forall (x : unit] from the goal *)
Ltac hstep_forall_unit :=
  hnf;
  lazymatch goal with
  | [ |- unit -> ?H ] => intros _
  | [ |- forall (y : finType_CS unit), ?H] => intros [] (* This is usually simplified to the first case with [cbn] *)
  | [ |- forall (y : unit), ?H] => intros []
  end.

Ltac hstep_pre := clear_abbrevs;cbn beta.
Ltac hstep_post := lazy beta.


Ltac hstep_Combinators := hstep_Seq || hstep_If || hstep_Switch || hstep_Return. (* Not [While]! *)
Ltac hstep_Lifts := (hstep_LiftTapes || hstep_ChangeAlphabet).
Ltac hstep := hstep_pre; (hstep_forall_unit || hstep_Combinators || hstep_Lifts || hstep_user); hstep_post.
Ltac hsteps := repeat first [hstep | hstep_post] (*execute "left to right" *).
Ltac hsteps_cbn := repeat (cbn; hstep). (* Calls [cbn] before each verification step *)


(* *** More automation for register specifications *)

Ltac openFoldRight :=
  try (hnf;
  lazymatch goal with
  | |- _ /\ _ => refine (conj _ _);[ | openFoldRight]
  | |- True => exact I
  end).

(* Proofs assertions like [tspec (SpecVector ?R) ?t] *)
Ltac tspec_solve :=
  lazymatch goal with
  | [ |- tspec (_,withSpace _ ?ss) ?t ] => (* We may unfold [withSpace] and simplify now *)
    eapply tspec_space_solve;openFoldRight;[ .. | intros i; destruct_fin i;
    cbn [tspec_single withSpace_single Vector.map Vector.nth Vector.case0 Vector.caseS]; try (simple apply I || contains_ext || isVoid_mono)]
  | [ |- tspec (?P,?R) ?t ] =>
    eapply tspec_solve;openFoldRight;[ .. | intros i; destruct_fin i;
    cbn [tspec_single Vector.nth Vector.case0 Vector.caseS]; try (simple apply I || contains_ext || isVoid_mono)]
  end.


(*
(* Pushes up [withSpace] in [tspec]s *)
Ltac tspec_withSpace_swap :=
  lazymatch goal with
  | [ H : ?t ≃≃ Frame (withSpace ?P ?ss) ?I (withSpace ?P' ?ss') |- _ ] =>
    apply tspec_Frame_withSpace in H; [ cbn in H; tspec_withSpace_swap |  now smpl_dupfree ]
  | [ H : ?t ≃≃ Downlift (withSpace ?P ?ss) ?I |- _ ] =>
    apply tspec_Downlift_withSpace in H; cbn in H; tspec_withSpace_swap
  | [ H : ?t ≃≃ LiftSpec ?I (withSpace ?P ?ss) |- _ ] =>
    apply tspec_LiftSpec_withSpace in H; cbn in H; tspec_withSpace_swap
  | _ => idtac
end.
*)

Ltac trySolveTrivEq := lazymatch goal with |- ?s = ?s => reflexivity | |- _ => idtac end.
(* Proofs assertions like [tspec (SpecVector ?R) ?t] given [tspec (SpecVector ?R') ?t]. Similar to [contains_ext] and [isVoid_mono]. *)
(* Normally, [eauto] should be able to solve this kind of goal. This tactic helps to find out if there is an error. *)
Ltac tspec_ext :=
  unfold_abbrev;intros;
  (*tspec_withSpace_swap;*)
  lazymatch goal with
  | [ |- Entails (tspec _) (tspec _) ] => simple apply EntailsI;intros ? ?; tspec_ext
  | [ |- forall t, t ≃≃ ?P -> t ≃≃ ?Q ] => (* idtac "tspec_ext: Branch 1 is depricated, pone should see Entails everywhere"; *)
    let Ht := fresh "H"t in
    intros t Ht; tspec_ext; eauto
  | [ H : tspec (_,withSpace _ ?ss) ?t |- tspec (_,withSpace _ ?ss') ?t ] =>
    apply tspec_space_ext with (1 := H);[ cbn [implList];intros; openFoldRight;trySolveTrivEq |
    ((now eauto)
     || (intros i; destruct_fin i;
        cbn [tspec_single withSpace_single Vector.nth Vector.case0 Vector.caseS];
        intros; try (simple apply I ||contains_ext || isVoid_mono)))]
  | [ H : tspec (?P',?R') ?t |- tspec (?P,?R) ?t ] => (* idtac "tspec_ext: Branch 2 is depricated, pone should see Entails everywhere"; *)
    apply tspec_ext with (1 := H);[ cbn [implList];intros; openFoldRight;trySolveTrivEq |
    ((now eauto)
     || (intros i; destruct_fin i;
        cbn [tspec_single Vector.nth Vector.case0 Vector.caseS];
        intros; try (simple apply I || contains_ext || isVoid_mono)))]
  end.

(* (* Maybe not a good idea *)
#[export] Hint Extern 10 => tspec_ext.
*)

Ltac underBinders t :=
  lazymatch goal with
  | |- forall x, _ => let x := fresh x in intros x;underBinders t;revert x
  | |- _ => t
  end.


Ltac introPure_prepare :=
  lazymatch goal with
  | |- Entails (tspec ((_,_))) _ => eapply tspec_introPure
  | |- Triple (tspec (?P,_)) _ _ => eapply Triple_introPure
  | |- TripleT (tspec (?P,_)) _ _ _ => eapply TripleT_introPure
  end;simpl implList at 1.

Tactic Notation "hintros" simple_intropattern_list(pat) := underBinders introPure_prepare;intros pat.

(* execute a single seq-step*)
Ltac hstep_seq :=
lazymatch goal with
| |- ?R (_;;_) _ => hstep;[(hstep;hsteps_cbn;cbn);let n := numgoals in (tryif ( guard n = 1) then try tspec_ext else idtac ) |cbn;try hstep_forall_unit | reflexivity..]
| |- ?R (LiftTapes _ _) _ => hsteps_cbn
| |- ?R (ChangeAlphabet _ _) _ => hsteps_cbn
end.