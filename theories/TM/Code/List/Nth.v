From Undecidability Require Import ProgrammingTools Hoare.
From Undecidability Require Import CaseNat CaseList CaseSum. (* [TM.Code.CaseSum] contains [Constr_Some] and [Constr_None]. *)


Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

 
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.

Set Default Proof Using "Type".

(** ** Other Implementation of [nth_error] *)

Section Nth'.

  (** In this implementation of [nth_error], instead of encoding an option to the output tape, we use the finite parameter to indicate whether the result is [Some] or [None]. The advantage is that the client doesn't have to add the option to its alphabet. *)

  Variable (sig sigX : finType) (X : Type) (cX : codable sigX X).
  (* Hypothesis (defX: inhabitedC sigX). *)

  Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).
  Local Instance retr_X_list' : Retract sigX sig := ComposeRetract retr1 (Retract_sigList_X _).

  (* Check _ : codable sig (list X). *)
  (* Check _ : codable sig nat. *)

  Definition Nth'_Step_size {sigX X : Type} {cX : codable sigX X} (n : nat) (l : list X) : Vector.t (nat -> nat) 3 :=
    match n, l with
    | S n', x :: l' =>
      [| CaseList_size0 x; S; CaseList_size1 x >> Reset_size x|]
    | 0, x :: x' =>
      [|fun s0 => CaseList_size0 x s0; id; fun s2 => CaseList_size1 x s2|]
    | 0, nil => [|id; id; id|]
    | S n', nil => [|id; fun s1 => S s1; id|]
    end.

  Definition Nth'_Step : pTM sig^+ (option bool) 3 :=
    If (LiftTapes (ChangeAlphabet CaseNat _) [|Fin1|])
       (If (LiftTapes (ChangeAlphabet (CaseList sigX) _) [|Fin0; Fin2|]) (* n = S n' *)
           (Return (LiftTapes (Reset _) [|Fin2|]) None) (* l = x :: l'; continue *)
           (Return Nop (Some false))) (* l = nil; return false *)
       (Relabel (LiftTapes (ChangeAlphabet (CaseList sigX) _) [|Fin0; Fin2|]) Some) (* n = 0 *)
  .


  Definition Nth'_Step_steps {sigX X : Type} {cX : codable sigX X} (l : list X) (n : nat) :=
    match n, l with
    | S n', x :: l' =>
      2 + CaseNat_steps + CaseList_steps_cons x + Reset_steps x
    | S n', nil =>
      2 + CaseNat_steps + CaseList_steps_nil
    | O, x :: l' =>
      1 + CaseNat_steps + CaseList_steps_cons x
    | O, nil =>
      1 + CaseNat_steps + CaseList_steps_nil
    end.

    Definition Nth'_Step_steps_CaseList (xs : list X) :=
      match xs with
      | x :: xs' => 1 + CaseList_steps_cons x + Reset_steps x
      | nil => 1 + CaseList_steps_nil
      end.
  
    Lemma Nth'_Step_SpecT_size (n : nat) (xs : list X) (ss : Vector.t nat 3) :
      TripleT
        (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ n; Void|]) ss))
        (Nth'_Step_steps xs n) Nth'_Step
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

  Fixpoint Nth'_Loop_size {sigX X : Type} {cX : codable sigX X} (n : nat) (l : list X) {struct n} : Vector.t (nat -> nat) 3 :=
    match n, l with
    | S n', x :: l' => Nth'_Step_size n l >>> Nth'_Loop_size n' l'
    | _, _ => Nth'_Step_size n l
    end.

  Definition Nth'_Loop := While Nth'_Step.

  Fixpoint Nth'_Loop_steps {sigX X : Type} {cX : codable sigX X} (l : list X) (n : nat) { struct l } :=
    match n, l with
    | S n', x :: l'  => S (Nth'_Step_steps l n) + Nth'_Loop_steps l' n' (* continue *)
    | S n', nil => Nth'_Step_steps l n (* return *)
    | O, x :: l' => Nth'_Step_steps l n (* return *)
    | O, nil => Nth'_Step_steps l n (* only [CaseNat] and [If] *)
    end.

    Lemma Nth'_Loop_SpecT_size xs n (ss : Vector.t nat 3) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ n; Void|]) ss))
      (Nth'_Loop_steps xs n) Nth'_Loop
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


  (** We don't want to save, but reset, [n]. *)
  Definition Nth' : pTM sig^+ bool 4 :=
    LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* Save l (on t0) to t3 *)
    If (LiftTapes (Nth'_Loop) [|Fin3; Fin1; Fin2|]) (* Execute the loop with the copy of l *)
       (Return (LiftTapes (Reset _) [|Fin3|];; (* Reset the copy of [l] *)
                LiftTapes (Reset _) [|Fin1|] (* Reset [n] *)
               ) true)
       (Return (LiftTapes (Reset _) [|Fin3|];; (* Reset the copy of [l] *)
                LiftTapes (Reset _) [|Fin1|] (* Reset [n] *)
               ) false)
  .

  Definition Nth'_size {sigX X : Type} {cX : codable sigX X} (l : list X) (n : nat) :=
    [| id;
       (Nth'_Loop_size n l)[@Fin1] >> Reset_size (n - (S (length l)));
       (Nth'_Loop_size n l)[@Fin2];
       CopyValue_size l >> (Nth'_Loop_size n l)[@Fin0] >> Reset_size (skipn (S n) l)
     |].

     
  Definition Nth'_steps {sigX X : Type} {cX : codable sigX X} (l : list X) (n : nat) :=
    3 + CopyValue_steps l + Nth'_Loop_steps l n + Reset_steps (skipn (S n) l) + Reset_steps (n - S (length l)).


     
  Lemma Nth'_SpecT_size (xs : list X) (n : nat) (ss : Vector.t nat 4) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ n; Void; Void|]) ss))
      (Nth'_steps xs n) Nth'
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


  Section Legacy.
    
    Definition Nth'_Rel : pRel sig^+ bool 4 :=
      fun tin '(yout, tout) =>
        forall (l : list X) (n : nat) s0 s1 s2 s3,
          tin[@Fin0] ≃(;s0) l ->
          tin[@Fin1] ≃(;s1) n ->
          isVoid_size tin[@Fin2] s2 ->
          isVoid_size tin[@Fin3] s3 ->
          match yout with
          | true =>
            exists (x : X),
            nth_error l n = Some x /\
            tout[@Fin0] ≃(;(Nth'_size l n)[@Fin0]s0) l /\
            isVoid_size tout[@Fin1] ((Nth'_size l n)[@Fin1]s1) /\
            tout[@Fin2] ≃(;(Nth'_size l n)[@Fin2]s2) x /\
            isVoid_size tout[@Fin3] ((Nth'_size l n)[@Fin3]s3)
          | false =>
            nth_error l n = None /\
            tout[@Fin0] ≃(;(Nth'_size l n)[@Fin0]s0) l /\
            isVoid_size tout[@Fin1] ((Nth'_size l n)[@Fin1]s1) /\
            isVoid_size tout[@Fin2] ((Nth'_size l n)[@Fin2]s2) /\
            isVoid_size tout[@Fin3] ((Nth'_size l n)[@Fin3]s3)
          end.

    Lemma Nth'_Realise : Nth' ⊨ Nth'_Rel.
    Proof.
      repeat (eapply RealiseIntroAll;intro). eapply Realise_monotone.
      -eapply TripleT_Realise. eapply Nth'_SpecT_size with (ss:=[|_;_;_;_|]).
      -unfold Nth'_Rel. intros ? [] H **. modpon H.
      {unfold "≃≃",withSpace;cbn. intros i; destruct_fin i;cbn. exact H3. all:eassumption. }
      repeat destruct _;unfold "≃≃",withSpace in H;cbn in H.
      2,3:contradiction.
      all:specializeFin H;eauto 6.
    Qed.


    Definition Nth'_T : tRel sig^+ 4 :=
      fun tin k => exists (l : list X) (n : nat),
          tin[@Fin0] ≃ l /\
          tin[@Fin1] ≃ n /\
          isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\
          Nth'_steps l n <= k.

    Lemma Nth'_Terminates : projT1 Nth' ↓ Nth'_T.
    Proof.
      repeat (eapply TerminatesInIntroEx;intro). eapply TerminatesIn_monotone.
      -eapply TripleT_TerminatesIn. eapply TripleT_RemoveSpace,Nth'_SpecT_size.
      -intros ? k H **. modpon H.
      split. 2:eassumption. 
      unfold "≃≃",withSpace;cbn. intros i; destruct_fin i;cbn. all:assumption. 
    Qed.
  End Legacy.

End Nth'.


Arguments Nth'_steps {sigX X cX} : simpl never.
Arguments Nth'_size {sigX X cX} : simpl never.