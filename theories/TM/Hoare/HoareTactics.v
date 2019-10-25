(** ** Very Convienient Verification Tactics for Hoare Logic *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import TM.Hoare.HoareLogic TM.Hoare.HoareCombinators TM.Hoare.HoareRegister.
From smpl Require Import Smpl.

(** We define tactics to "execute" the machine step-by-step during the verification. It uses [smpl] to be user-extensible. *)



(** Checks whether the given term contains an evar *)
Ltac contains_evar e :=
  match e with
  | context [?x] => is_evar x
  end.

(** Check if the goal triple is with space *)
Ltac triple_with_space :=
  lazymatch goal with
  | [ |- context [withSpace] ] => idtac
  end.



(** *** Smpl setup *)

(* For user extensions, like in [TM_Correct] *)
Smpl Create hstep_smpl.
Ltac hstep_smpl := smpl hstep_smpl.


(** *** Combinators *)

(** There is no tactic for While. *)


Ltac hstep_Seq :=
  match goal with
  | [ |- Triple ?P (?M1;; ?M2) ?Q ] => eapply Seq_Spec
  | [ |- TripleT ?P ?k (?M1;; ?M2) ?Q ] => eapply Seq_SpecT
  end.

(** Note: We often want to specify the running times ([k2] and [k3]) of [M2] and [M3] manually. For that, the user has to apply [If_SpecT] manually. *)
(** If desired, the user can apply the weak version [If_SpecT_weak] or [If_SpecT_weak'] manually. *)
Ltac hstep_If :=
  lazymatch goal with
  | [ |- Triple ?P (If ?M1 ?M2 ?M3) ?Q ] => eapply If_Spec
  | [ |- TripleT ?P ?k (If ?M1 ?M2 ?M3) ?Q ] => eapply If_SpecT
  end.

Ltac hstep_Switch :=
  lazymatch goal with
  | [ |- Triple ?P (Switch ?M1 ?M2) ?Q ] => eapply Switch_Spec
  | [ |- TripleT ?P ?k (Switch ?M1 ?M2) ?Q ] => eapply Switch_SpecT
  end.


(** For [Return], we may have to use the rule [Return_Spec_con]. *)
Ltac hstep_Return :=
  lazymatch goal with
  | [ |- Triple ?P (Return ?M ?x) ?Q ] =>
    tryif contains_evar Q then (eapply Return_Spec)
    else (eapply Return_Spec_con)
  | [ |- TripleT ?P ?k (Return ?M ?x) ?Q ] =>
    tryif contains_evar Q then (eapply Return_SpecT)
    else (eapply Return_SpecT_con)

  | [ |- Triple ?P (Relabel ?M ?f) ?Q ] =>
    tryif contains_evar Q then (eapply Relabel_Spec)
    else (eapply Relabel_Spec_con)
  | [ |- TripleT ?P ?k (Relabel ?M ?f) ?Q ] =>
    tryif contains_evar Q then (eapply Relabel_SpecT)
    else (eapply Relabel_SpecT_con)
  end.



(** ** Lifts *)

(** The rules for the lifts have been implemented for register machines only *)
(** We have special rules for specifications with space; and we also have to check whether the post-condition already is instantiated. *)
Ltac hstep_LiftTapes :=
  lazymatch goal with
  | [ |- Triple ?P (?M @ ?I) ?Q ] =>
    tryif contains_evar Q then (* The post-condition is yet to be instantiated. *)
      (tryif triple_with_space then (eapply LiftTapes_Spec_space; [smpl_dupfree | ])
        else (eapply LiftTapes_Spec; [smpl_dupfree | ]))
    else (* Otherwise, we have to use the Consequence rule *)
      (tryif triple_with_space then (eapply LiftTapes_Spec_space_con; [smpl_dupfree | | ])
        else (eapply LiftTapes_Spec_con; [smpl_dupfree | | ]))
  | [ |- TripleT ?P ?k (?M @ ?I) ?Q ] =>
    tryif contains_evar Q then
      (tryif triple_with_space then (eapply LiftTapes_SpecT_space; [smpl_dupfree | ])
        else (eapply LiftTapes_SpecT; [smpl_dupfree | ]))
    else
      (tryif triple_with_space then (eapply LiftTapes_SpecT_space_con; [smpl_dupfree | | ])
        else (eapply LiftTapes_SpecT_con; [smpl_dupfree | | ]))
  end.


(** [ChangeAlphabet] is similar to [LiftTapes], but we always have to apply at least [Consequence_pre]. We also have specialised rules for space. *)
Ltac hstep_ChangeAlphabet :=
  lazymatch goal with
  | [ |- Triple ?P (?M ⇑ ?I) ?Q ] =>
    tryif contains_evar Q then (* The post-condition is yet to be instantiated. *)
      (tryif triple_with_space then (eapply ChangeAlphabet_Spec_space_pre; [ | ])
        else (eapply ChangeAlphabet_Spec_pre; [ | ]))
    else (* Otherwise, we have to use the Consequence rule *)
      (tryif triple_with_space then (eapply ChangeAlphabet_Spec_space_pre_post; [ | | ])
        else (eapply ChangeAlphabet_Spec_pre_post; [ | | ]))
  | [ |- TripleT ?P ?k (?M ⇑ ?I) ?Q ] =>
    tryif contains_evar Q then
      (tryif triple_with_space then (eapply ChangeAlphabet_SpecT_space_pre; [ | ])
        else (eapply ChangeAlphabet_SpecT_pre; [ | ]))
    else
      (tryif triple_with_space then (eapply ChangeAlphabet_SpecT_space_pre_post; [ | | ])
        else (eapply ChangeAlphabet_SpecT_pre_post; [ | | ]))
  end.

(*
Ltac hstep_ChangeAlphabet :=
  lazymatch goal with
  | [ |- Triple ?P (?M ⇑ ?I) ?Q ] =>
    tryif contains_evar Q then (eapply ChangeAlphabet_Spec)
    else (eapply ChangeAlphabet_Spec_con; [ | ])
  | [ |- TripleT ?P ?k (?M ⇑ ?I) ?Q ] =>
    tryif contains_evar Q then (eapply ChangeAlphabet_SpecT)
    else (eapply ChangeAlphabet_SpecT_pre_post; [ | ])
  end.
*)


(*
(** After applying lifts, we have to push [withSpace] to the front of the premise again. *)
Ltac hstep_withSpace_swap :=
  lazymatch goal with
  (** Rule for the tapes lift *)
  | [ |- Triple  (tspec (Frame (withSpace ?P ?ss) ?I (withSpace ?P' ?ss')))    ?M ?Q ] => eapply Triple_Frame_withSpace;  [now smpl_dupfree | ]
  | [ |- TripleT (tspec (Frame (withSpace ?P ?ss) ?I (withSpace ?P' ?ss'))) ?k ?M ?Q ] => eapply TripleT_Frame_withSpace; [now smpl_dupfree | ]

  | [ |- Triple  (tspec (Downlift (withSpace ?P ?ss) ?I))    ?M ?Q ] => eapply Triple_Downlift_withSpace
  | [ |- TripleT (tspec (Downlift (withSpace ?P ?ss) ?I)) ?k ?M ?Q ] => eapply TripleT_Downlift_withSpace

  (** Rules for the alphabet lift *)
  | [ |- Triple  (tspec (LiftSpec ?I (withSpace ?P ?ss)))    ?M ?Q ] => eapply Triple_LiftSpec_withSpace
  | [ |- TripleT (tspec (LiftSpec ?I (withSpace ?P ?ss))) ?k ?M ?Q ] => eapply TripleT_LiftSpec_withSpace
  end.
*)


(** *** Custom machines *)

(** We have to be carefull with [Nop] and custom machines, because usually the postcondition is already instantiated. *)

(** The user only needs to specify the Termination rule. If the user wants to prove partial correctness, it it first checked whether
there is a corresponding Termination lemma. The tactic also takes care of whether we first have to apply the consequence rule. *)

Ltac hstep_user :=
  lazymatch goal with
  | [ |- Triple ?P ?M ?Q ] => (* Without time *)
    tryif contains_evar Q then
      (tryif triple_with_space then
          (* Without time, but with space *)
          ((eapply TripleT_Triple; hstep_smpl) (* Weaken a registered rule with time and space *)
           || (hstep_smpl))
        else ((eapply TripleT_Triple; eapply TripleT_RemoveSpace; now (intros; hstep_smpl)) (* Weaken a registered rule with time and space *)
              || (eapply Triple_RemoveSpace; now (intros; hstep_smpl)) (* Weaken a registered rule without time but with space *)
              || (eapply TripleT_Triple; hstep_smpl) (* Weaken a registered rule with time but without space *)
              || (hstep_smpl))) (* A registered rule without time and without space *)
    else (eapply Consequence_post; [ hstep_user | ]) (* First apply the consequence rule, then try again *)
  | [ |- TripleT ?P ?k ?M ?Q ] => (* With time *)
    tryif contains_evar Q then
      (tryif triple_with_space then hstep_smpl (* Apply the rule with time and space *)
        else (eapply TripleT_RemoveSpace; now (intros; hstep_smpl)) (* Weaken a rule with time and space *)
             || (hstep_smpl))
    else (eapply ConsequenceT_post; [ hstep_user | ]) (* First apply the consequence rule, then try again *)
  end.

(** Example: [Nop] *)

Ltac hstep_Nop :=
  lazymatch goal with
  (* | [ |- Triple ?P Nop ?Q ] => eapply Nop_Spec *)
  | [ |- TripleT ?P ?k Nop ?Q ] => eapply Nop_SpecT
  end.

Smpl Add hstep_Nop : hstep_smpl.


(** *** Verification step tactic *)

(** Removes [forall (x : unit] from the goal *)
Ltac hstep_forall_unit :=
  lazymatch goal with
  | [ |- unit -> ?H ] => intros _
  | [ |- forall (y : finType_CS unit), ?H] => intros [] (* This is usually simplified to the first case with [cbn] *)
  | [ |- forall (y : unit), ?H] => intros []
  end.


Ltac hstep_Combinators := hstep_Seq || hstep_If || hstep_Switch || hstep_Return. (* Not [While]! *)
Ltac hstep_Lifts := (hstep_LiftTapes || hstep_ChangeAlphabet).
Ltac hstep := (*repeat hstep_withSpace_swap;*) (hstep_forall_unit || hstep_Combinators || hstep_Lifts || hstep_user)(*; repeat hstep_withSpace_swap*).
Ltac hsteps := repeat hstep.
Ltac hsteps_cbn := repeat (cbn; hstep). (* Calls [cbn] before each verification step *)


(** *** More automation for register specifications *)


(** Proofs assertions like [tspec (SpecVector ?R) ?t] *)
Ltac tspec_solve :=
  lazymatch goal with
  | [ |- tspec (SpecVector ?R) ?t ] =>
    eapply tspec_solve; intros i; destruct_fin i;
    cbn [tspec_single Vector.nth Vector.case0 Vector.caseS]; try (contains_ext || isVoid_mono)
  | [ |- tspec (withSpace (SpecVector ?R) ?ss) ?t ] => (* We may unfold [withSpace] and simplify now *)
    eapply tspec_space_solve; intros i; destruct_fin i;
    cbn [tspec_single withSpace_single Vector.map Vector.nth Vector.case0 Vector.caseS]; try (contains_ext || isVoid_mono)
  end.


(*
(** Pushes up [withSpace] in [tspec]s *)
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


(** Proofs assertions like [tspec (SpecVector ?R) ?t] given [tspec (SpecVector ?R') ?t]. Similar to [contains_ext] and [isVoid_mono]. *)
(** Normally, [eauto] should be able to solve this kind of goal. This tactic helps to find out if there is an error. *)
Ltac tspec_ext :=
  (*tspec_withSpace_swap;*)
  lazymatch goal with
  | [ |- forall t, t ≃≃ ?P -> t ≃≃ ?Q ] =>
    let Ht := fresh "H"t in
    intros t Ht; tspec_ext; eauto
  | [ H : tspec (SpecVector ?R') ?t |- tspec (SpecVector ?R) ?t ] =>
    apply tspec_ext with (1 := H);
    ((now eauto)
     || (intros i; destruct_fin i;
        cbn [tspec_single Vector.nth Vector.case0 Vector.caseS];
        intros; try (contains_ext || isVoid_mono)))
    | [ H : tspec (withSpace (SpecVector ?R') ?ss) ?t |- tspec (withSpace (SpecVector ?R) ?ss') ?t ] =>
    apply tspec_space_ext with (1 := H);
    ((now eauto)
     || (intros i; destruct_fin i;
        cbn [tspec_single withSpace_single Vector.nth Vector.case0 Vector.caseS];
        intros; try (contains_ext || isVoid_mono)))
  end.

(* (* Maybe not a good idea *)
Hint Extern 10 => tspec_ext.
*)
