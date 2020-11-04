From PslBase Require Import Bijection. (* [injective] *)
From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import TM.Code.CompareValue.
From Undecidability Require Import TM.Code.CasePair TM.Code.CaseList.
From Undecidability.TM.Hoare Require Import Hoare HoareLegacy.


Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(** * Lookup an entry in an associative list *)

Section LookupAssociativeList.
  
  Variable (sigX sigY : finType).
  Variable (X : eqType) (Y : Type) (cX : codable sigX X) (cY : codable sigY Y).

  Notation sig := (sigList (sigPair sigX sigY)).

  Hypothesis (cX_injective : injective cX).

  Fixpoint lookup (x : X) (xs : list (X * Y)) {struct xs} : option Y :=
    match xs with
    | nil => None
    | (x', y) :: xs' => if Dec (x = x') then Some y else lookup x xs'
    end.

  Local Definition retr_sig_sigX : Retract sigX sig := _.
  Local Definition retr_sig_sigY : Retract sigY sig := _.

  Definition Lookup_Step : pTM sig^+ (option bool) 4 :=
    If (CaseList (FinType(EqType(sigPair sigX sigY))) @ [|Fin0; Fin2|] )
       (CasePair _ _  ⇑ _ @ [|Fin2; Fin3|];;
        If (CompareValues _ ⇑ retr_sig_sigX  @ [|Fin1; Fin3|])
           (Return (MoveValue _ @ [|Fin2; Fin1|];; Reset _ @ [|Fin3|];; Reset _ @ [|Fin0|]) (Some true))
           (Return (Reset _ @ [|Fin3|];; Reset _ @ [|Fin2|]) None))
       (Return (ResetEmpty1 _ @ [|Fin0|]) (Some false)).


  Definition Lookup_Step_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x:X) : Vector.t (nat->nat) 4 :=
    match xs with
    | (x', y) :: xs' =>
      if Dec (x=x')
      then [| (*0*) CaseList_size0 (x', y) >> Reset_size xs';
              (*1*) MoveValue_size_y y x; (* [CompareValue] doesn't use space *)
              (*2*) CaseList_size1 (x', y) >> CasePair_size0 x' >> MoveValue_size_x y;
              (*3*) CasePair_size1 x' >> Reset_size x' |]
      else [| (*0*) CaseList_size0 (x',y);
              (*1*) id; (* [CompareValue] doesn't use space *)
              (*2*) CaseList_size1 (x',y) >> CasePair_size0 x' >> Reset_size y;
              (*3*) CasePair_size1 x' >> Reset_size x' |]
    | nil => [| ResetEmpty1_size; id; id; id|]
    end.    

  Definition Lookup_Step_steps_Compare {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x x' : X) (y : Y) (xs : list (X*Y)) :=
    if Dec (x=x')
    then 2 + MoveValue_steps y x + Reset_steps x' + Reset_steps xs
    else 1 + Reset_steps x' + Reset_steps y.

  Definition Lookup_Step_steps_CaseList {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) :=
    match xs with
    | nil => ResetEmpty1_steps
    | (x',y) :: xs' => 2 + CompareValues_steps x x' + CasePair_steps x' + Lookup_Step_steps_Compare x x' y xs'
    end.

  Definition Lookup_Step_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) :=
    1 + CaseList_steps xs + Lookup_Step_steps_CaseList xs x.

  Lemma Lookup_Step_SpecT_space (xs : list (X*Y)) (x : X) (ss : Vector.t nat 4) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ x; Void; Void|]) ss))
      (Lookup_Step_steps xs x)
      Lookup_Step
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
    start_TM.
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
          -- unfold Lookup_Step_steps_Compare. dec_pos (x=x'). lia.
          -- cbn. intros _. tspec_ext.
        * cbn. (* "Else": We have [x<>x'] *) decide (x=x') as [ | Hx]; cbn in *; auto.
          hstep. hstep.
          -- hstep. cbn. eapply Reset_SpecT_space with (X := X).
          -- cbn. intros _. hstep. cbn. apply Reset_SpecT_space with (X := Y).
          -- unfold Lookup_Step_steps_Compare. dec_neg (x=x'). reflexivity.
          -- cbn. intros _. tspec_ext.
        * intros tin ymid tmid H1 H2. cbn in *. destruct ymid; decide (x=x') as [Hx|Hx]; cbn in *; auto.
      + cbn. lia.
    - cbn. (* The top-most "Else": We have [xs=nil] *) destruct xs as [ | ]; cbn in *; auto.
      hstep. hstep; cbn. eapply ResetEmpty1_SpecT_space with (X := list (X*Y)). reflexivity. cbn. eauto.
    - (* Finall running time *) intros tin yout tout _ _. destruct yout; reflexivity.
  Qed.

  Definition Lookup_Loop := While Lookup_Step.


  Fixpoint Lookup_Loop_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) : Vector.t (nat->nat) 4 :=
    match xs with
    | nil => Lookup_Step_size xs x
    | (x',y) :: xs' =>
      if Dec(x=x')
      then Lookup_Step_size xs x
      else Lookup_Step_size xs x >>> Lookup_Loop_size xs' x
    end.
    

  Fixpoint Lookup_Loop_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (xs : list (X*Y)) { struct xs } :=
    match xs with
    | nil => Lookup_Step_steps xs x
    | (x',y) :: xs' => if Dec(x=x')
                      then Lookup_Step_steps xs x
                      else 1 + Lookup_Step_steps xs x + Lookup_Loop_steps x xs'
    end.

  Lemma Lookup_Loop_SpecT_space (xs : list (X*Y)) (x : X) (ss : Vector.t nat 4) :
  TripleT
    (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ x; Void; Void|]) ss))
    (Lookup_Loop_steps x xs) Lookup_Loop
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

  Definition Lookup : pTM sig^+ bool 5 :=
    CopyValue _ @ [|Fin0; Fin4|];; Lookup_Loop @ [|Fin4; Fin1; Fin2; Fin3|].

  Definition Lookup_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) : Vector.t (nat->nat) 5 :=
    ([|CopyValue_size xs|] @>> [|Fin4|]) >>>
    (Lookup_Loop_size xs x @>>[|Fin4; Fin1; Fin2; Fin3|]).

  
  Definition Lookup_Rel : pRel sig^+ bool 5 :=
    fun tin '(yout, tout) =>
      forall (xs : list (X*Y)) (x : X) (s0 s1 s2 s3 s4 : nat),
        let size := Lookup_size xs x in
        tin[@Fin0] ≃(;s0) xs ->
        tin[@Fin1] ≃(;s1) x ->
        isVoid_size tin[@Fin2] s2 -> isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 ->
        match yout, lookup x xs with
        | true, Some y =>
          tout[@Fin0] ≃(;size@>Fin0 s0) xs /\
          tout[@Fin1] ≃(;size@>Fin1 s1) y /\
          isVoid_size tout[@Fin2] (size@>Fin2 s2) /\
          isVoid_size tout[@Fin3] (size@>Fin3 s3) /\
          isVoid_size tout[@Fin4] (size@>Fin4 s4)
        | false, None =>
          tout[@Fin0] ≃(;size@>Fin0 s0) xs /\
          tout[@Fin1] ≃(;size@>Fin1 s1) x /\
          isVoid_size tout[@Fin2] (size@>Fin2 s2) /\
          isVoid_size tout[@Fin3] (size@>Fin3 s3) /\
          isVoid_size tout[@Fin4] (size@>Fin4 s4)
        | _, _ => False
        end.


  Definition Lookup_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (xs : list (X*Y)) :=
    1 + CopyValue_steps xs + Lookup_Loop_steps x xs.

    Lemma Lookup_SpecT_space (xs : list (X*Y)) (x : X) (ss : Vector.t nat 5) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ x; Void; Void; Void|]) ss))
      (Lookup_steps x xs) Lookup
      (fun yout =>
         tspec
           (withSpace
              match yout, lookup x xs with
              | true, Some y => SpecVector [|Contains _ xs; Contains _ y; Void; Void; Void|]
              | false,  None => SpecVector [|Contains _ xs; Contains _ x; Void; Void; Void|]
              | _, _ => SpecFalse
              end (appSize (Lookup_size xs x) ss))).
  Proof.
    start_TM.
    unfold Lookup. hsteps_cbn; cbn.
    apply CopyValue_SpecT_size with (X := list (X*Y)).
    cbn. apply Lookup_Loop_SpecT_space.
    intros yout tout H. cbn in *.
    destruct yout, (lookup x xs); cbn in *; eauto.
    reflexivity.
  Qed.

  (* Legacy Lemma *)
  Lemma Lookup_Realise : Lookup ⊨ Lookup_Rel.
  Proof.
    repeat (eapply RealiseIntroAll;intro). eapply Realise_monotone.
    -eapply TripleT_Realise, (Lookup_SpecT_space x x0 [|x1;x2;x3;x4;x5|]).
    -intros ? [] H **. modpon H.
    {unfold "≃≃",withSpace;cbn. intros i; destruct_fin i;cbn. all:assumption. }
    repeat destruct _;unfold "≃≃",withSpace in H;cbn in H.
    2,3:contradiction.
    all:specializeFin H;tauto.
  Qed.

  Definition Lookup_T : tRel sig^+ 5 :=
    fun tin k =>
      exists (xs : list (X*Y)) (x : X),
        tin[@Fin0] ≃ xs /\
        tin[@Fin1] ≃ x /\
        isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\
        Lookup_steps x xs <= k.

  (* legacy Lemma *)
  Lemma Lookup_Terminates : projT1 Lookup ↓ Lookup_T.
  Proof.
    repeat (eapply TerminatesInIntroEx;intro). eapply TerminatesIn_monotone.
    -eapply TripleT_TerminatesIn. eapply TripleT_RemoveSpace,Lookup_SpecT_space.
    -intros ? k H **. modpon H.
    split. 2:eassumption. 
    unfold "≃≃",withSpace;cbn. intros i; destruct_fin i;cbn. all:assumption. 
  Qed.

End LookupAssociativeList.

Arguments Lookup_steps {sigX sigY X Y cX cY} : simpl never.
Arguments Lookup_size {sigX sigY X Y cX cY} : simpl never.

Ltac hstep_LookupAssociativeList :=
  match goal with
  | [ |- TripleT ?P ?k (Lookup _ _) ?Q ] => eapply Lookup_SpecT_space
  end.
