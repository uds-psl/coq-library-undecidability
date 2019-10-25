(** * Combinators *)

(** Export Modules for Combinators *)
From Undecidability Require Export Switch If SequentialComposition StateWhile While Mirror.

(** ** Simple Combinators *)

(** Identity operator *)
Section Id.
  (** The purpose of this operator is to deactivate [TM_Correct]. *)
  Variable (sig : finType) (n : nat).
  Variable (F : finType).

  Variable (pM : pTM sig F n).

  Definition Id := pM.
End Id.



(** Simple operator to change the labelling function *)
Section Relabel.
  Variable (sig : finType) (n : nat).
  Variable F F' : finType.
  Variable pM : { M : mTM sig n & states M -> F }.
  Variable p : F -> F'.

  Definition Relabel : pTM sig F' n :=
    (projT1 pM; fun q => p (projT2 pM q)).

  Lemma Relabel_Realise R :
    pM ⊨ R ->
    Relabel ⊨ ⋃_y (R |_ y) ||_(p y).
  Proof.
    intros HRel.
    intros tin k outc HLoop.
    hnf in HRel. specialize HRel with (1 := HLoop).
    hnf. exists (projT2 pM (cstate outc)). hnf. cbn. auto.
  Qed.

  Lemma Relabel_RealiseIn R k :
    pM ⊨c(k) R ->
    Relabel ⊨c(k) ⋃_y (R |_ y) ||_(p y).
  Proof. firstorder. Qed.

  Lemma Relabel_Terminates T :
    projT1 pM ↓ T ->
    projT1 Relabel ↓ T.
  Proof. firstorder. Qed.

End Relabel.

Arguments Relabel : simpl never.


(** Special case of the above operator, where we just fix a label *)
Section Return.

  Variable (sig : finType) (n : nat).
  Variable F : finType.
  Variable pM : { M : mTM sig n & states M -> F }.
  Variable F' : finType.
  Variable p : F'.

  Definition Return := Relabel pM (fun _ => p).

  Lemma Return_Realise R :
    pM ⊨ R ->
    Return ⊨ (⋃_f (R |_ f)) ||_ p.
  Proof. intros. intros tin k outc HLoop. hnf. split; hnf; eauto. exists (projT2 pM (cstate outc)). hnf. eauto. Qed.

  Lemma Return_RealiseIn R k :
    pM ⊨c(k) R ->
    Return ⊨c(k) (⋃_f (R |_ f)) ||_ p.
  Proof. firstorder. Qed.

  Lemma Return_Terminates T :
    projT1 pM ↓ T ->
    projT1 Return ↓ T.
  Proof. firstorder. Qed.

End Return.

Arguments Return : simpl never.



(** ** Tactic Support *)


(** Helper tactics for match *)

(** This tactic destructs a variable recursivle and shelves each goal where it couldn't destruct the variable further. The purpose of this tactic is to pre-instantiate functions to relations with holes of the form [Param -> Rel _ _]. We need this for the [Switch] Machine.
The implementation of this tactic is quiete uggly but works for parameters with up to 9 constructor arguments. This tactic may generates a lot of warnings, which can be ignored. *)
Ltac destruct_shelve e :=
  cbn in e;
  idtac "Input:";
  print_type e;
  idtac "Output:";
  print_goal_cbn; 
  let x1 := fresh "x" in
  let x2 := fresh "x" in
  let x3 := fresh "x" in
  let x4 := fresh "x" in
  let x5 := fresh "x" in
  let x6 := fresh "x" in
  let x7 := fresh "x" in
  let x8 := fresh "x" in
  let x9 := fresh "x" in
  first [ destruct e as [x1|x2|x3|x4|x5|x6|x7|x8|x9]; idtac e "has 9 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5 | try destruct_shelve x6 | try destruct_shelve x7 | try destruct_shelve x8 | try destruct_shelve x9]; shelve
        | destruct e as [x1|x2|x3|x4|x5|x6|x7|x8]; idtac e "has 8 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5 | try destruct_shelve x6 | try destruct_shelve x7 | try destruct_shelve x8]; shelve
        | destruct e as [x1|x2|x3|x4|x5|x6|x7]; idtac e "has 7 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5 | try destruct_shelve x6 | try destruct_shelve x7]; shelve
        | destruct e as [x1|x2|x3|x4|x5|x6]; idtac e "has 6 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5 | try destruct_shelve x6]; shelve
        | destruct e as [x1|x2|x3|x4|x5]; idtac e "has 5 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5]; shelve
        | destruct e as [x1|x2|x3|x4]; idtac e "has 4 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4]; shelve
        | destruct e as [x1|x2|x3]; idtac e "has 3 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3]; shelve
        | destruct e as [x1|x2]; idtac e "has 2 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2]; shelve
        | destruct e as [x1]; idtac e "has 1 constructors"; [ try destruct_shelve x1 ]; shelve
        | destruct e as []; idtac e "has 0 constructors"; shelve
        ]
.
  

(* Eval simpl in ltac:(intros ?e; destruct_shelve e) : (option (bool + (bool + (bool + bool)))) -> Rel _ _. *)


Ltac smpl_match_case_solve_RealiseIn :=
  eapply RealiseIn_monotone'; [ | shelve].

Ltac smpl_match_RealiseIn :=
  lazymatch goal with
  | [ |- Switch ?M1 ?M2 ⊨c(?k1) ?R] =>
    is_evar R;
    let tM2 := type of M2 in
    let x := fresh "x" in
    match tM2 with
    | ?F -> _ =>
      eapply (Switch_RealiseIn
                (F := FinType(EqType F))
                (R2 := ltac:(now (print_goal; intros x; destruct_shelve x))));
      [
        smpl_match_case_solve_RealiseIn
      | intros x; repeat destruct _; smpl_match_case_solve_RealiseIn
      ]
    end
  end
.

Ltac smpl_match_Realise :=
  lazymatch goal with
  | [ |- Switch ?M1 ?M2 ⊨ ?R] =>
    is_evar R;
    let tM2 := type of M2 in
    let x := fresh "x" in
    match tM2 with
    | ?F -> _ =>
      eapply (Switch_Realise
                (F := FinType(EqType F))
                (R2 := ltac:(now (intros x; destruct_shelve x))));
      [
      | intros x; repeat destruct _
      ]
    end
  end.


Ltac smpl_match_Terminates :=
  lazymatch goal with
  | [ |- projT1 (Switch ?M1 ?M2) ↓ ?R] =>
    is_evar R;
    let tM2 := type of M2 in
    let x := fresh "x" in
    match tM2 with
    | ?F -> _ =>
      eapply (Switch_TerminatesIn
                (F := FinType(EqType F))
                (T2 := ltac:(now (intros x; destruct_shelve x))));
      [ (* show weak realisation of the machine over which is matched *)
      | (* Show termination of the machine over which is matched *)
      | intros x; repeat destruct _ (* Show termination of each case-machine *)
      ]
    end
  end.



(* There is no rule for [Id] on purpose. *)
Ltac smpl_TM_Combinators :=
  lazymatch goal with
  | [ |- Switch _ _ ⊨ _] => smpl_match_Realise
  | [ |- Switch _ _ ⊨c(_) _] => smpl_match_RealiseIn
  | [ |- projT1 (Switch _ _) ↓ _] => smpl_match_Terminates
  | [ |- If _ _ _ ⊨ _] => eapply If_Realise
  | [ |- If _ _ _ ⊨c(_) _] => eapply If_RealiseIn
  | [ |- projT1 (If _ _ _) ↓ _] => eapply If_TerminatesIn
  | [ |- Seq _ _ ⊨ _] => eapply Seq_Realise
  | [ |- Seq _ _ ⊨c(_) _] => eapply Seq_RealiseIn
  | [ |- projT1 (Seq _ _) ↓ _] => eapply Seq_TerminatesIn
  | [ |- While _ ⊨ _] => eapply While_Realise
  | [ |- projT1 (While _) ↓ _] => eapply While_TerminatesIn
  | [ |- StateWhile _ _ ⊨ _] => eapply StateWhile_Realise
  | [ |- projT1 (StateWhile _ _) ↓ _] => eapply StateWhile_TerminatesIn
  | [ |- Relabel _ _ ⊨ _] => eapply Relabel_Realise
  | [ |- Relabel _ _ ⊨c(_) _] => eapply Relabel_RealiseIn
  | [ |- projT1 (Relabel _ _) ↓ _] => eapply Relabel_Terminates
  | [ |- Return _ _ ⊨ _] => eapply Return_Realise
  | [ |- Return _ _ ⊨c(_) _] => eapply Return_RealiseIn
  | [ |- projT1 (Return _ _) ↓ _] => eapply Return_Terminates
  end.

Smpl Add smpl_TM_Combinators : TM_Correct.