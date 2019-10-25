From PslBase Require Import Bijection. (* [injective] *)
From Undecidability.TM Require Import ProgrammingTools.
From Undecidability.TM Require Import LookupAssociativeListTM.
From Undecidability.TM Require Import Hoare.Hoare.
From Undecidability.TM Require Import Code.CaseList.

From Undecidability.TM Require Import CompareValue CasePair.

Arguments plus : simpl never.
Arguments mult : simpl never.


Section LookupAssociativeList.
  
  Variable (sigX sigY : finType).
  Variable (X : eqType) (Y : Type) (cX : codable sigX X) (cY : codable sigY Y).

  Notation sig := (sigList (sigPair sigX sigY)).

  Hypothesis (cX_injective : injective cX).

  Local Existing Instance LookupAssociativeListTM.retr_sig_sigX.
  Local Existing Instance LookupAssociativeListTM.retr_sig_sigY.

  (*
  Definition Lookup_Step : pTM sig^+ (option bool) 4 :=
    If (CaseList (FinType(EqType(sigPair sigX sigY))) @ [|Fin0; Fin2|] )
       (CasePair _ _  ⇑ _ @ [|Fin2; Fin3|];;
        If (CompareValues _ ⇑ retr_sig_sigX  @ [|Fin1; Fin3|])
           (Return (MoveValue _ @ [|Fin2; Fin1|];; Reset _ @ [|Fin3|];; Reset _ @ [|Fin0|]) (Some true))
           (Return (Reset _ @ [|Fin3|];; Reset _ @ [|Fin2|]) None))
       (Return (ResetEmpty1 _ @ [|Fin0|]) (Some false)).
   *)

  Lemma Lookup_Step_SpecT_space (xs : list (X*Y)) (x : X) (ss : Vector.t nat 4) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ x; Void; Void|]) ss))
      (Lookup_Step_steps xs x)
      (Lookup_Step sigX sigY)
      (fun yout =>
         tspec (withSpace
           (match yout, xs with
            | Some false, nil => SpecVector [|Void; Contains _ x; Void; Void|]
            | _, (x',y) :: xs' =>
              match yout, (Dec (x=x') : bool) with
              | Some true, true =>
                SpecVector [|Void; Contains _ y; Void; Void|]
              | None, false =>
                SpecVector [|Contains _ xs'; Contains _ x; Void; Void|]
              | _, _ => SpecFalse
              end
            | _, _ => SpecFalse
            end) (appSize (Lookup_Step_size xs x) ss))).
  Proof.
    unfold Lookup_Step. unfold Lookup_Step_size; cbn.
    eapply If_SpecT with (k1 := CaseList_steps xs) (k2 := Lookup_Step_steps_CaseList xs x) (k3 := Lookup_Step_steps_CaseList xs x).
    - hstep; cbn. apply CaseList_SpecT_size.
    - (* First "Then"; we have [xs = (x',y) :: xs']. *)
      cbn. destruct xs as [ | (x', y) xs']; cbn in *; auto.
      hstep.
      + (* CasePair *) cbn.
        hstep; cbn. hstep; cbn. hstep; cbn. cbn. tspec_ext.
      + cbn. intros _.
        eapply If_SpecT with (k1 := CompareValues_steps x x') (k2 := Lookup_Step_steps_Compare x x' y xs') (k3 := Lookup_Step_steps_Compare x x' y xs').
        * hsteps_cbn; cbn. apply CompareValue_SpecT_size with (X := X). assumption. cbn. tspec_ext.
        * (* Second "Then"; we have [x=x'] *) decide (x=x') as [Hx | ]; cbn in *; auto.
          hstep. (* Return *) hstep. (* Seq *)
          -- (* MoveValue *) hstep; cbn. apply MoveValue_SpecT_size with (X := Y) (Y := X).
          -- cbn. intros _. hstep. (* Seq *)
             ++ (* Reset X *) hstep; cbn.  apply Reset_SpecT_space with (X := X).
             ++ (* Reset Y *) cbn. intros _. hstep. cbn. apply Reset_SpecT_space with (X := list (X*Y)).
             ++ reflexivity.
          -- unfold Lookup_Step_steps_Compare. dec_pos (x=x'). omega.
          -- cbn. intros _. tspec_ext.
        * cbn. (* "Else": We have [x<>x'] *) decide (x=x') as [ | Hx]; cbn in *; auto.
          hstep. hstep.
          -- hstep. cbn. eapply Reset_SpecT_space with (X := X).
          -- cbn. intros _. hstep. cbn. apply Reset_SpecT_space with (X := Y).
          -- unfold Lookup_Step_steps_Compare. dec_neg (x=x'). reflexivity.
          -- cbn. intros _. tspec_ext.
        * intros tin ymid tmid H1 H2. cbn in *. destruct ymid; decide (x=x') as [Hx|Hx]; cbn in *; auto.
      + cbn. omega.
    - cbn. (* The top-most "Else": We have [xs=nil] *) destruct xs as [ | ]; cbn in *; auto.
      hstep. hstep. cbn. eapply ResetEmpty1_SpecT_space with (X := list (X*Y)). reflexivity. cbn. eauto.
    - (* Finall running time *) intros tin yout tout _ _. destruct yout; reflexivity.
  Qed.

  Lemma Lookup_Loop_SpecT_space (xs : list (X*Y)) (x : X) (ss : Vector.t nat 4) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ x; Void; Void|]) ss))
      (Lookup_Loop_steps x xs) (Lookup_Loop sigX sigY)
      (fun yout =>
         tspec
           (withSpace
              match yout, lookup x xs with
              | true, Some y => SpecVector [|Void; Contains _ y; Void; Void|]
              | false,  None => SpecVector [|Void; Contains _ x; Void; Void|]
              | _, _ => SpecFalse
              end (appSize (Lookup_Loop_size xs x) ss))).
  Proof.
    unfold Lookup_Loop.
    eapply While_SpecT with (P := fun '(xs, x, ss) => _) (Q := fun '(xs, x, ss) => _) (R := fun '(xs, x, ss) => _) (g := fun '(xs,x,ss) => _) (f := fun '(xs,x,ss) => _)
                            (x := (xs,x,ss)); clear x xs ss; intros ((xs, x), ss).
    - apply Lookup_Step_SpecT_space.
    - intros [] tmid tout H1 H2.
      destruct xs as [ | (x', y) xs']; cbn in *; auto.
      + decide (x = x'); cbn in *; eauto.
      + destruct xs as [ | (x', y) xs']; cbn in *; auto.
    - cbn. intros tin tmid Htin Hmid.
      destruct xs as [ | (x', y) xs']; cbn in *; auto.
      decide (x = x'); cbn in *; eauto.
      eexists (_, _, _); cbn. repeat split.
      + eauto.
      + reflexivity.
      + eauto.
  Qed.

  Lemma Lookup_SpecT_space (xs : list (X*Y)) (x : X) (ss : Vector.t nat 5) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ x; Void; Void; Void|]) ss))
      (Lookup_steps x xs) (Lookup sigX sigY)
      (fun yout =>
         tspec
           (withSpace
              match yout, lookup x xs with
              | true, Some y => SpecVector [|Contains _ xs; Contains _ y; Void; Void; Void|]
              | false,  None => SpecVector [|Contains _ xs; Contains _ x; Void; Void; Void|]
              | _, _ => SpecFalse
              end (appSize (Lookup_size xs x) ss))).
  Proof.
    unfold Lookup. hsteps_cbn; cbn.
    apply CopyValue_SpecT_size with (X := list (X*Y)).
    cbn. apply Lookup_Loop_SpecT_space.
    intros yout tout H. cbn in *.
    destruct yout, (lookup x xs); cbn in *; eauto.
    reflexivity.
  Qed.

End LookupAssociativeList.


Ltac hstep_LookupAssociativeList :=
  match goal with
  | [ |- TripleT ?P ?k (Lookup _ _) ?Q ] => eapply Lookup_SpecT_space
  end.
