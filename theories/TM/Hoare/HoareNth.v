(* ** Verification of [Nth] with the Hoare framework *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import Hoare.Hoare.
From Undecidability Require Import CaseNat CaseList.
From Undecidability Require Import ListTM.

Arguments plus : simpl never.
Arguments mult : simpl never.


Section Nth.

  Variable (sig sigX : finType) (X : Type) (cX : codable sigX X).
  Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).
  Local Existing Instance retr_X_list'.

  Definition Nth'_Step_steps_CaseList (xs : list X) :=
    match xs with
    | x :: xs' => 1 + CaseList_steps_cons x + Reset_steps x
    | nil => 1 + CaseList_steps_nil
    end.

  Definition Nth'_Step_steps' (xs : list X) (n : nat) :=
    match n with
    | S n' => 1 + CaseNat_steps + Nth'_Step_steps_CaseList xs
    | O' => 1 + CaseNat_steps + CaseList_steps xs
    end.

  Lemma Nth'_Step_SpecT_size (n : nat) (xs : list X) (ss : Vector.t nat 3) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ n; Void|]) ss))
      (Nth'_Step_steps xs n) (Nth'_Step retr1 retr2)
      (fun yout =>
         tspec (withSpace
                  match yout, n, xs with
                  | None,       S n', x::xs' => SpecVector [|Contains _ xs'; Contains _ n'; Void|]
                  | Some true,     0, x::xs' => SpecVector [|Contains _ xs'; Contains _ 0;  Contains _ x|]
                  | Some false,    O,   nil => SpecVector [|Contains _ nil; Contains _ 0;  Void|]
                  | Some false, S n',   nil => SpecVector [|Contains _ nil; Contains _ n'; Void|]
                  | _, _, _ => SpecFalse
                  end (appSize (Nth'_Step_size n xs) ss))).
  Proof.
    start_TM.
    unfold Nth'_Step.
    eapply If_SpecT with (k1 := CaseNat_steps) (k2 := Nth'_Step_steps_CaseList xs) (k3 := CaseList_steps xs).
    - hstep; cbn.
      hstep; cbn. (* or [eapply ChangeAlphabet_SpecT_space_pre.] *)
      hstep; cbn. cbn. tspec_ext.
    - cbn. destruct n as [ | n']; cbn in *; auto.
      (** Like in the Realisation proof, we make a case-distinction over the value of [xs]. *)
      destruct xs as [ | x xs']; cbn in *; auto.
      + eapply If_SpecT with (k2 := 0).
        * hstep; cbn. hstep; cbn. hstep; cbn. cbn. tspec_ext.
        * cbn. auto. (* The "Then" case of the "If CaseList". We are not in this state, since [xs=nil]. *)
        * cbn. hstep; cbn. hstep; cbn. cbn. intros _. tspec_ext.
        * cbn. intros tin yout tout. destruct yout; cbn in *; auto.
      + eapply If_SpecT.
        * hstep; cbn. hstep; cbn. hstep; cbn. cbn. tspec_ext.
        * cbn. hstep; cbn. hstep; cbn. apply Reset_SpecT_space. cbn. intros _. tspec_ext.
        * cbn. auto. (* The "Else" case of the "If CaseList". We are not in this state, since [xs=x::xs']. *)
        * cbn. intros tin yout tout. destruct yout; cbn in *; auto.
    - cbn. destruct n as [ | n']; cbn in *; auto.
      hstep; cbn. hstep; cbn. hstep; cbn. hstep; cbn.
      cbn. tspec_ext.
      intros yout tout. destruct yout, xs as [ | x xs']; cbn in *; auto.
      + intros. tspec_ext.
      + intros. tspec_ext.
    - intros ? ? ? ? ?. destruct yout, n as [ | n'], xs as [ | x xs']; cbn in *; auto.
  Qed.

  Lemma Nth'_Loop_SpecT_size xs n (ss : Vector.t nat 3) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ n; Void|]) ss))
      (Nth'_Loop_steps xs n) (Nth'_Loop retr1 retr2)
      (fun yout =>
         tspec
           (withSpace
              match yout, nth_error xs n with
              | true, Some x => SpecVector [|Contains _ (skipn (S n) xs); Contains _ (n - (S (length xs))); Contains _ x|]
              | false, None  => SpecVector [|Contains _ (skipn (S n) xs); Contains _ (n - (S (length xs))); Void|]
              | _, _ => SpecFalse
              end
              (appSize (Nth'_Loop_size n xs) ss))).
  Proof.
    eapply While_SpecT with (P := fun '(xs,n,ss) => _) (Q := fun '(xs,n,ss) => _) (R := fun '(xs,n,ss) => _) (g := fun '(xs,n,ss) => _) (f := fun '(xs,n,ss) => _) (x := (xs,n,ss));
      clear xs n ss; intros ((xs,n),ss).
    - apply Nth'_Step_SpecT_size.
    - cbn. intros yout tmid tout H1 H2.
      destruct yout, n as [ | n'], xs as [ | x xs']; cbn in *; auto.
      replace (n' - 0) with n' by lia. auto.
    - cbn. intros yout tmid tout H1.
      destruct n as [ | n'], xs as [ | x xs']; cbn in *; auto.
      eexists (xs', n', _). repeat split; cbn.
      + eauto.
      + reflexivity.
      + eauto.
  Qed.

  Lemma Nth'_SpecT_size (xs : list X) (n : nat) (ss : Vector.t nat 4) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ n; Void; Void|]) ss))
      (Nth'_steps xs n) (Nth' retr1 retr2)
      (fun yout =>
         tspec (withSpace
                  match yout, nth_error xs n with
                  | true, Some x => SpecVector [|Contains _ xs; Void; Contains _ x; Void|]
                  | false, None => SpecVector [|Contains _ xs; Void; Void; Void|]
                  | _, _ => SpecFalse
                  end (appSize (Nth'_size xs n) ss))).
  Proof.
    start_TM.
    unfold Nth'.
    hstep; cbn. hstep; cbn. apply CopyValue_SpecT_size.
    cbn. intros _. eapply If_SpecT; cbn.
    - hstep; cbn. eapply ConsequenceT_pre. apply Nth'_Loop_SpecT_size. tspec_ext. reflexivity.
    - cbn. destruct (nth_error xs n) as [ x | ]; cbn in *; auto.
      hstep; cbn. hstep; cbn. hstep; cbn. apply Reset_SpecT_space with (X := list X).
      cbn. intros []. eauto. hstep; cbn. apply Reset_SpecT_space with (X := nat). reflexivity.
      cbn. intros _. auto.
    - cbn. destruct (nth_error xs n) as [ x | ]; cbn in *; auto.
      hstep; cbn. hstep; cbn. hstep; cbn. apply Reset_SpecT_space with (X := list X).
      cbn. intros []. eauto. hstep; cbn. apply Reset_SpecT_space with (X := nat). reflexivity.
      cbn. intros _. auto.
    - cbn. intros tin yout tout ? ?. cbn. destruct yout; cbn in *; auto.
    - unfold Nth'_steps. cbn. lia.
  Qed.


End Nth.
