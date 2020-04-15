From Undecidability Require Import ProgrammingTools.

(** * Constructor and Deconstructor Machines for Sum Types and Option Types *)

Lemma tl_length (X : Type) (xs : list X) :
  length (tl xs) = pred (length xs).
Proof. destruct xs; cbn; auto. Qed.


Section CaseSum.

  Variable X Y : Type.

  (** ** Deconstructor for Sum Types *)

  Variable (sigX sigY : finType).
  Hypothesis (codX : codable sigX X) (codY : codable sigY Y).

  Definition CaseSum_Rel : Rel (tapes (sigSum sigX sigY)^+ 1) (bool * tapes ((sigSum sigX sigY)^+) 1) :=
    Mk_R_p (
        fun tin '(yout, tout) =>
          forall (s : X + Y) (ss : nat),
            tin ≃(;ss) s ->
            match yout, s with
            | true, inl x => tout ≃(;S ss) x
            | false, inr y => tout ≃(;S ss) y
            | _, _ => False
            end).


  Definition CaseSum : pTM (sigSum sigX sigY)^+ bool 1 :=
    Move R;; (* skip the [START] symbol *)
    Switch (ReadChar) (* read the "constructor" symbol *)
          (fun o => match o with (* Write a new [START] symbol and terminate in the corresponding label *)
                 | Some (inr sigSum_inl) => Return (Write (inl START)) true  (* inl *)
                 | Some (inr sigSum_inr) => Return (Write (inl START)) false (* inr *)
                 | _ => Return (Nop) true (* invalid input *)
                 end).

  Definition CaseSum_steps := 5.

  Lemma CaseSum_Sem : CaseSum ⊨c(CaseSum_steps) CaseSum_Rel.
  Proof.
    unfold CaseSum_steps. eapply RealiseIn_monotone.
    { unfold CaseSum. TM_Correct. }
    { Unshelve. 4,10,11: constructor. all: cbn. all: omega. }
    {
      intros tin (yout&tout) H.
      intros s ss HEncS. destruct HEncS as (ls&HEncS&Hss). TMSimp; clear_trivial_eqs. clear HEncS tin.
      destruct s as [x|y]; cbn in *; TMSimp.
      - (* s = inl x *) hnf. eexists. split. cbn. rewrite !List.map_map. f_equal. cbn. omega.
      - (* s = inr y *) hnf. eexists. split. cbn. rewrite !List.map_map. f_equal. cbn. omega.
    }
  Qed.

  (** ** Constructors for Sum Types *)
  Section SumConstr.


    Definition Constr_inl_Rel : Rel (tapes (sigSum sigX sigY)^+ 1) (unit * tapes (sigSum sigX sigY)^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall (x:X) (ss:nat), tin ≃(;ss) x -> tout ≃(;pred ss) inl x)).

    Definition Constr_inr_Rel : Rel (tapes (sigSum sigX sigY)^+ 1) (unit * tapes (sigSum sigX sigY)^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall (y:Y) (ss:nat), tin ≃(;ss) y -> tout ≃(;pred ss) inr y)).

    Definition Constr_inl : pTM (sigSum sigX sigY)^+ unit 1 :=
      WriteMove (inr sigSum_inl) L;; Write (inl START).

    Definition Constr_inr : pTM (sigSum sigX sigY)^+ unit 1 :=
      WriteMove (inr sigSum_inr) L;; Write (inl START).


    Definition Constr_inl_steps := 3.
    Lemma Constr_inl_Sem : Constr_inl ⊨c(Constr_inl_steps) Constr_inl_Rel.
    Proof.
      unfold Constr_inl_steps. eapply RealiseIn_monotone.
      { unfold Constr_inl. TM_Correct. }
      { cbn. reflexivity. }
      {
        intros tin (()&tout) H.
        cbn. intros x s HEncX. destruct HEncX as (ls&HEncX). TMSimp; clear_trivial_eqs.
        hnf. simpl_tape. eexists. split.
        - cbn. rewrite !List.map_map. f_equal.
        - cbn. rewrite tl_length. omega.
      }
    Qed.

    Definition Constr_inr_steps := 3.
    Lemma Constr_inr_Sem : Constr_inr ⊨c(Constr_inl_steps) Constr_inr_Rel.
    Proof.
      unfold Constr_inr_steps. eapply RealiseIn_monotone.
      { unfold Constr_inr. TM_Correct. }
      { cbn. reflexivity. }
      {
        intros tin (()&tout) H.
        cbn. intros y ss HEncY. destruct HEncY as (ls&HEncY&Hss). TMSimp; clear_trivial_eqs.
        hnf. simpl_tape. eexists. split.
        - cbn. rewrite !List.map_map. f_equal.
        - cbn. rewrite tl_length. omega.
      }
    Qed.

  End SumConstr.

End CaseSum.

Arguments CaseSum : simpl never.
Arguments Constr_inl : simpl never.
Arguments Constr_inr : simpl never.

(** ** Tactic Support for Sum Types *)

Ltac smpl_TM_CaseSum :=
  lazymatch goal with
  | [ |- CaseSum _ _ ⊨ _ ] => eapply RealiseIn_Realise; apply CaseSum_Sem
  | [ |- CaseSum _ _ ⊨c(_) _ ] => apply CaseSum_Sem
  | [ |- projT1 (CaseSum _ _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply CaseSum_Sem
  | [ |- Constr_inr _ _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_inr_Sem
  | [ |- Constr_inr _ _ ⊨c(_) _ ] => apply Constr_inr_Sem
  | [ |- projT1 (Constr_inr _ _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_inr_Sem
  | [ |- Constr_inl _ _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_inl_Sem
  | [ |- Constr_inl _ _ ⊨c(_) _ ] => apply Constr_inl_Sem
  | [ |- projT1 (Constr_inl _ _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_inl_Sem
  end.

Smpl Add smpl_TM_CaseSum : TM_Correct.





Section CaseOption.

  (* Switching of option reduces to matching of sums with [Empty_set] *)

  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (codX : codable sigX X).

  (* Compute encode (None : option nat). *)
  (* Compute encode (Some 42). *)

  (** ** Deconstructor for Option Types *)

  Let sig := FinType (EqType (sigSum sigX (FinType(EqType Empty_set)))).
  Let tau := FinType (EqType (sigOption sigX)).

  Definition CaseOption_size_Some := S.
  Definition CaseOption_size_None := S >> S.

  Definition CaseOption_Rel : Rel (tapes tau^+ 1) (bool * tapes tau^+ 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              forall (o : option X) (s : nat),
                tin ≃(;s) o ->
                match yout, o with
                | true, Some x => tout ≃(;CaseOption_size_Some s) x
                | false, None => isRight_size tout (CaseOption_size_None s)
                | _, _ => False
                end).

  Local Program Instance Retract_sigOption_sigSum :
    Retract (sigSum sigX Empty_set) (sigOption sigX) :=
    {|
      Retr_f x := match x : (sigSum sigX (FinType (EqType Empty_set))) with
                  | sigSum_X a => sigOption_X a
                  | sigSum_Y b => match b with end
                  | sigSum_inl => sigOption_Some
                  | sigSum_inr => sigOption_None
                  end;
      Retr_g y := match y with
                  | sigOption_X a => Some (sigSum_X a)
                  | sigOption_Some => Some (sigSum_inl)
                  | sigOption_None => Some (sigSum_inr)
                  end;
      |}.
  Next Obligation.
    abstract now intros x y; split;
      [ now destruct y; intros H; inv H
      | intros ->; now destruct x as [ a | [] | | ]
      ].
  Defined.


  Definition CaseOption : pTM (sigOption sigX)^+ bool 1 :=
    If (ChangeAlphabet (CaseSum (sigX) (FinType (EqType Empty_set))) _)
       (Return Nop true)
       (Return (ResetEmpty _) false).

  Definition opt_to_sum (o : option X) : X + unit :=
    match o with
    | Some x => inl x
    | None => inr tt
    end.

  Definition CaseOption_steps := 7.
  
  Lemma CaseOption_Sem :
    CaseOption ⊨c(CaseOption_steps) CaseOption_Rel.
  Proof.
    unfold CaseOption_steps. eapply RealiseIn_monotone.
    { unfold CaseOption. TM_Correct. unfold ChangeAlphabet. TM_Correct.
      - apply ResetEmpty_Sem with (X := unit).
    }
    { cbn. reflexivity. }
    {
      intros tin (yout&tout) H. intros o s HEncO.
      cbn in *.
      destruct H; TMSimp; unfold tau in *.
      { (* "Then" case *)
        (* This part is the same for both branches *)
        simpl_tape in H. cbn in *.
        specialize (H (opt_to_sum o) s). spec_assert H.
        { 
          simpl_surject. contains_ext.
          destruct o; cbn; f_equal. rewrite !List.map_map. apply List.map_ext. cbv; auto.
        }
        destruct o as [ x | ]; cbn in *; auto.
        simpl_tape in H; cbn in *; simpl_surject. contains_ext.
      }
      { (* "Else" case *)
        simpl_tape in H. cbn in *.
        specialize (H (opt_to_sum o) s). spec_assert H.
        { 
          simpl_surject. contains_ext.
          destruct o; cbn; f_equal. rewrite !List.map_map. apply List.map_ext. cbv; auto.
        }
        destruct o as [ x | ]; cbn in *; auto.
        simpl_tape in H; cbn in *; simpl_surject.
        specialize H1 with (x := tt). modpon H1.
        (* We know now that o = None *)
        eauto.
      }
    }
  Qed.

  (** ** Constructors for Option Types *)

  Definition Constr_Some_Rel : Rel (tapes tau^+ 1) (unit * tapes tau^+ 1) :=
    Mk_R_p (ignoreParam(
                fun tin tout =>
                  forall (x : X) (s : nat),
                    tin ≃(;s) x ->
                    tout ≃(;pred s) Some x)).

  Definition Constr_Some : pTM (sigOption sigX)^+ unit 1 :=
    ChangeAlphabet (Constr_inl sigX (FinType (EqType Empty_set))) _.

  Definition Constr_Some_steps := 3.
  Lemma Constr_Some_Sem : Constr_Some ⊨c(Constr_Some_steps) Constr_Some_Rel.
  Proof.
    unfold Constr_Some_steps. eapply RealiseIn_monotone.
    { unfold Constr_Some. unfold ChangeAlphabet. TM_Correct. }
    { cbn. reflexivity. }
    {
      intros tin ((), tout) H.
      intros x s HEncX. TMSimp.
      simpl_tape in H. cbn in H.
      unfold tape_contains in *.
      modpon H.
      contains_ext.
      cbn. f_equal. rewrite !List.map_map. apply List.map_ext. auto.
    }
  Qed.

  
  Definition Constr_None_Rel : Rel (tapes tau^+ 1) (unit * tapes tau^+ 1) :=
    Mk_R_p
      (ignoreParam
         (fun tin tout =>
            forall (s : nat),
              isRight_size tin s ->
              tout ≃(; pred s) None)).

  Definition Constr_None : pTM tau^+ unit 1 := WriteValue [ sigOption_None ].

  Goal Constr_None = WriteMove (inl STOP) L;; WriteMove (inr sigOption_None) L;; Write (inl START).
  Proof. reflexivity. Qed.
    
  Definition Constr_None_steps := 5.
  Lemma Constr_None_Sem : Constr_None ⊨c(Constr_None_steps) Constr_None_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Constr_None. TM_Correct. }
    { cbn. reflexivity. }
    { intros tin ((), tout) H. intros s HRight.
      cbn in H. specialize H with (x := None). modpon H. cbn in H. contains_ext. unfold WriteValue_size. omega.
    }
  Qed.

End CaseOption.

Arguments CaseOption : simpl never.
Arguments Constr_None : simpl never.
Arguments Constr_Some : simpl never.


(** ** Tactic Support for Option Types *)

Ltac smpl_TM_CaseOption :=
  lazymatch goal with
  | [ |- CaseOption _ ⊨ _ ] => eapply RealiseIn_Realise; apply CaseOption_Sem
  | [ |- CaseOption _ ⊨c(_) _ ] => apply CaseOption_Sem
  | [ |- projT1 (CaseOption _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply CaseOption_Sem
  | [ |- Constr_None _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_None_Sem
  | [ |- Constr_None _ ⊨c(_) _ ] => apply Constr_None_Sem
  | [ |- projT1 (Constr_None _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_None_Sem
  | [ |- Constr_Some _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_Some_Sem
  | [ |- Constr_Some _ ⊨c(_) _ ] => apply Constr_Some_Sem
  | [ |- projT1 (Constr_Some _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_Some_Sem
  end.

Smpl Add smpl_TM_CaseOption : TM_Correct.
