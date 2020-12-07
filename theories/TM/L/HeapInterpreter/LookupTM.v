(* * Heap Lookup *)

From Undecidability Require Import TM.Code.ProgrammingTools LM_heap_def.
From Undecidability.TM.L Require Import Alphabets.
From Undecidability Require Import TM.Code.ListTM TM.Code.CasePair TM.Code.CaseSum TM.Code.CaseNat Hoare.Hoare.

Set Default Proof Using "Type".
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Section Lookup.

  (* There is no need to save [n]. [H] must be saved. We use the [Nth'] machine, because we don't want to introduce an additional [sigOption sigHEnt] to the alphabet. [Nth'] also doesn't save [a] (which is the parameter of [Nth'] here, not [n]). [Lookup] will overwrite and reset the variables [a] and [n], but save [H] (which is saved by [Nth']). *)

(* We could define [Lookup] over the alphabet [sigHeap], however, in the step machine, we want to read [a] and [n] from a different closure alphabet (sigList sigHClos). [a] is read from an address of a closure and [n] from a variable of this closure, and the output closure will also be copied to this alphabet. *)


  Variable sigLookup : finType.
  
  Variable retr_clos_lookup : Retract sigHClos sigLookup.
  Variable retr_heap_lookup : Retract sigHeap sigLookup.


  (*
There are (more than) three possible ways how to encode [nat] on the [Heap] alphabet [sigLookup]:

- 1: as a heap address of a closure on the stack alphabet
- 2: as a variable of a command inside a closure of the closure input alphabet
- 3: as a "next" address of an heap entry

[a] is stored in the second way and [n] in the third way.
*)

  (* No 1 *)
  Definition retr_nat_clos_ad : Retract sigNat sigHClos :=
    Retract_sigPair_X _ _.
  Definition retr_nat_lookup_clos_ad : Retract sigNat sigLookup :=
    ComposeRetract retr_clos_lookup retr_nat_clos_ad.

  (* No 2 *)
  Definition retr_nat_clos_var : Retract sigNat sigHClos :=
    Retract_sigPair_Y _ _.
  Definition retr_nat_lookup_clos_var : Retract sigNat sigLookup :=
    ComposeRetract retr_clos_lookup retr_nat_clos_var.

  (* No 3 *)
  Definition retr_nat_heap_entry : Retract sigNat sigHeap :=
    Retract_sigList_X (Retract_sigOption_X (Retract_sigPair_Y _ (Retract_id _))).
  Local Definition retr_nat_lookup_entry : Retract sigNat sigLookup :=
    ComposeRetract retr_heap_lookup retr_nat_heap_entry.

  
  (* Encoding of a closure on the heap alphabet *)
  Definition retr_clos_heap : Retract sigHClos sigHeap := _.
  Definition retr_clos_lookup_heap : Retract sigHClos sigLookup := ComposeRetract retr_heap_lookup retr_clos_heap.

  Definition retr_hent_heap : Retract sigHEntr sigHeap := _.
  Local Definition retr_hent_lookup : Retract sigHEntr sigLookup := ComposeRetract retr_heap_lookup retr_hent_heap.

  Definition retr_hent'_heap : Retract sigHEntr' sigHeap := _.
  Local Definition retr_hent'_lookup : Retract sigHEntr' sigLookup := ComposeRetract retr_heap_lookup retr_hent'_heap.
  
  (*
  Tapes:
  t0: H
  t1: a
  t2: n
  t3: out
  t4: internal tape
  *)

  Definition Lookup_Step : pTM sigLookup^+ (option bool) 5 :=
    If (Nth' retr_heap_lookup retr_nat_lookup_clos_ad @ [|Fin0; Fin1; Fin4; Fin3|])
       (If (CaseOption sigHEntr'_fin ⇑ retr_hent_lookup @ [|Fin4|])
           (CasePair sigHClos_fin sigHAdd_fin ⇑ retr_hent'_lookup @ [|Fin4; Fin3|];;
            If (CaseNat ⇑ retr_nat_lookup_clos_var @ [|Fin2|])
               (Return (CopyValue _ @ [|Fin4; Fin1|];; (* n = S n' *)
                        Translate retr_nat_lookup_entry retr_nat_lookup_clos_ad @ [|Fin1|];;
                        Reset _ @ [|Fin4|];;
                        Reset _ @ [|Fin3 |])
                       None) (* continue *)
               (Return (Reset _ @ [|Fin4|];; (* n = 0 *)
                        Reset _ @ [|Fin2|];;
                        Translate retr_clos_lookup_heap retr_clos_lookup @ [|Fin3|])
                       (Some true))) (* return true *)
           (Return Nop (Some false))) (* return false *)
       (Return Nop (Some false)) (* return false *)
  .


  Definition Lookup_Step_size (H : Heap) (a n : nat) : Vector.t (nat->nat) 5 :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | S n' =>
        [|(* 0 *) Nth'_size H a @>Fin0;
          (* 1 *) Nth'_size H a @>Fin1 >> CopyValue_size b;
          (* 2 *) S;
          (* 3 *) Nth'_size H a @>Fin3 >> CasePair_size1 g >> Reset_size g;
          (* 4 *) Nth'_size H a @>Fin2 >> CaseOption_size_Some >> CasePair_size0 g >> Reset_size b|]
      | 0 =>
        [|(* 0 *) Nth'_size H a @>Fin0;
          (* 1 *) Nth'_size H a @>Fin1;
          (* 2 *) Reset_size 0;
          (* 3 *) Nth'_size H a @>Fin3 >> CasePair_size1 g;
          (* 4 *) Nth'_size H a @>Fin2 >> CaseOption_size_Some >> CasePair_size0 g >> Reset_size b|]
      end
    | _ => default (* not specified *)
    end.


  
  Local Definition Lookup_Step_steps_CaseNat (n: nat) (e': HClos * HAdd) :=
    let (g,b) := (fst e', snd e') in
    match n with
    | S _ => 1 + CopyValue_steps b + 1 + Translate_steps b + 1 + Reset_steps b + Reset_steps g
    | O => 1 + Reset_steps b + 1 + Reset_steps 0 + Translate_steps g
    end.

  Local Definition Lookup_Step_steps_CaseOption (n:nat) (e: HEntr) :=
    match e with
    | Some ((g, b) as e') => 1 + CasePair_steps g + 1 + CaseNat_steps + Lookup_Step_steps_CaseNat n e'
    | None => 0
    end.

  Local Definition Lookup_Step_steps_Nth' H a n :=
    match nth_error H a with
    | Some e => 1 + CaseOption_steps + Lookup_Step_steps_CaseOption n e
    | None => 0
    end.

  Definition Lookup_Step_steps (H: Heap) (a: HAdd) (n: nat) :=
    1 + Nth'_steps H a + Lookup_Step_steps_Nth' H a n.



  
  Lemma Lookup_Step_SpecT_space H a n ss:
  TripleT
    ≃≃([],withSpace [| ≃(_) H ; ≃(retr_nat_lookup_clos_ad) a;≃(retr_nat_lookup_clos_var) n;Void;Void |] ss)
    (Lookup_Step_steps H a n) Lookup_Step
    (fun yout => ≃≃([yout = match nth_error (A:=HEntr) H a with Some (Some _ ) => match n with 0 => Some true | _ => None end | _ => Some false end]
       ,withSpace
       match nth_error (A:=HEntr) H a with
        Some (Some (g,b) ) =>
        match n with
        | 0 => [| ≃(_) H; Void;Void;≃(retr_clos_lookup) g;Void|]
        | S n' => [| ≃(_) H;≃(retr_nat_lookup_clos_ad) b;≃(retr_nat_lookup_clos_var) n';Void;Void|]
        end
       | _ => SpecVTrue
       end (appSize (Lookup_Step_size H a n) ss))).
  Proof.
    unfold Lookup_Step. remember (Lookup_Step_size H a n) as F eqn:HF.
    eapply If_SpecTReg with (k2:= match nth_error H a with Some (Some (g,b)) => _ | Some _ => _ | None => _ end) (k3:=0).
    now hsteps_cbn.
    2:{ destruct nth_error. hintros [=]. cbn. hsteps_cbn. tspec_ext. }
    {
      unfold Lookup_Step_size in HF.
      cbn. destruct nth_error as [ h | ];hintros [=];[].
      eapply If_SpecTReg  with (k2:= match h with Some (g,b)=> _ |  None => _ end) (k3:=0).
      { hsteps_cbn. cbn. tspec_ext. } 
      2:{ cbn. destruct h; hintros [=]. hsteps_cbn. cbn. tspec_ext. }
      2:{ cbn. intros ? ->. destruct h as [[]| ]. 2:reflexivity. shelve. }
      cbn. destruct h as [[g b] | ];hintros [=];[].
      hstep. { hsteps_cbn. cbn. tspec_ext. }
      2:{cbn. unfold CasePair_steps. reflexivity. } 
      intros ?. hstep. { hsteps_cbn. cbn. tspec_ext. }
      - cbn. hintros Hn. destruct n. easy.
        hsteps_cbn. cbn.
        { eapply ConsequenceT_pre. refine (Translate_SpecT_size _ _ _ _ [| _|]). 3:tspec_ext. reflexivity. }
        1-3:reflexivity.
        subst F. cbn. tspec_ext.
      - cbn. hintros ->.
        hsteps_cbn. cbn. { eapply ConsequenceT_pre. refine (Translate_SpecT_size _ _ _ _ [| _|]). 3:tspec_ext. reflexivity. }
        1-2:reflexivity.
        subst F. cbn; tspec_ext.
      - cbn. intros b0 Hb. refine (_ : _ <= match n with 0 => _ | _ => _ end).
        destruct b0, n. 1,4:exfalso;clear - Hb;lia. all:reflexivity.  
    }
    Unshelve. 5:reflexivity. 2,3:exact 0.
    cbn. intros ? ->. unfold Lookup_Step_steps,Lookup_Step_steps_Nth'. destruct nth_error as [[[[] ]| ]| ]. all:cbn. 2,3:nia. unfold CasePair_steps. destruct n; cbn. all:rewrite !Nat.add_assoc. all:reflexivity. 
  Qed.
    

  Definition Lookup := While Lookup_Step.


  Fixpoint Lookup_size (H : Heap) (a n : nat) {struct n} : Vector.t (nat -> nat) 5 :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | S n' => Lookup_Step_size H a n >>> Lookup_size H b n'
      | 0 => Lookup_Step_size H a n
      end
    | _ => default (* not specified *)
    end.

  Lemma Lookup_size_eq (H : Heap) (a n : nat) :
    Lookup_size H a n =
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | S n' => Lookup_Step_size H a n >>> Lookup_size H b n'
      | 0 => Lookup_Step_size H a n
      end
    | _ => default (* not specified *)
    end.
  Proof. destruct n; auto. Qed.

  Definition Lookup_Rel : pRel sigLookup^+ bool 5 :=
    fun tin '(yout, tout) =>
      forall (H: Heap) (a n: nat) (s0 s1 s2 s3 s4 : nat),
        let size := Lookup_size H a n in
        tin[@Fin0] ≃(;s0) H ->
        tin[@Fin1] ≃(retr_nat_lookup_clos_ad ; s1) a ->
        tin[@Fin2] ≃(retr_nat_lookup_clos_var; s2) n ->
        isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 ->
        match yout with
        | true =>
          exists g,
          lookup H a n = Some g /\
          tout[@Fin0] ≃(;size @>Fin0 s0) H /\ (* [H] is saved *)
          isVoid_size tout[@Fin1] (size @>Fin1 s1) /\ (* [a] is discarded *)
          isVoid_size tout[@Fin2] (size @>Fin2 s2) /\ (* [n] is discarded *)
          tout[@Fin3] ≃(retr_clos_lookup; size @>Fin3 s3) g /\ (* result *)
          isVoid_size tout[@Fin4] (size @>Fin4 s4) (* internal tape *)
        | false =>
          lookup H a n = None (* Tapes are not specified *)
        end.

  Arguments Lookup_Step_size : simpl never.
    
  Fixpoint Lookup_steps (H : Heap) (a : HAdd) (n : nat) : nat :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Lookup_Step_steps H a n
      | S n' => 1 + Lookup_Step_steps H a n + Lookup_steps H b n'
      end
    | _ => Lookup_Step_steps H a n
    end.

      
  Lemma Lookup_SpecT_space H a n ss:
  TripleT
    ≃≃([],withSpace [| ≃(_) H ; ≃(retr_nat_lookup_clos_ad) a;≃(retr_nat_lookup_clos_var) n;Void;Void |] ss)
    (Lookup_steps H a n) Lookup
    (fun yout => ≃≃([yout = match lookup H a n with Some _ => true | _ => false end]
    , withSpace match lookup H a n with Some g => [| ≃(_) H;Void;Void;≃(retr_clos_lookup) g; Void|] | _ => SpecVTrue end (appSize (Lookup_size H a n) ss))).
  Proof.
    unfold Lookup.
    eapply While_SpecTReg with (PRE := fun '(a,n,ss) => (_,_))(INV := fun '(a,n,ss) y => ([y = match nth_error H a with
    | Some (Some _) => match n with | 0 => Some true | S _ => None end | _ => Some false end],_)) (POST := fun '(a,n,ss) y => (_,_))
       (f__step := fun '(a,n,ss) => Lookup_Step_steps H a n ) (f__loop := fun '(a,n,ss) => _ ) (x:= (a,n,ss));clear a n ss;intros [[a n] ss].
    { eapply ConsequenceT. eapply Lookup_Step_SpecT_space. 2:intros. 1,2:cbn - [appSize SpecVTrue].  1,2:now tspec_ext. reflexivity. }   
    all:cbn - [SpecVTrue appSize Lookup_size]. 
    remember (Lookup_size H a n) as F eqn:HF. remember (Lookup_steps H a n) as F' eqn:HF'. split.
    -destruct n;unfold Lookup_size in HF;unfold Lookup_steps in HF';fold Lookup_size in HF;fold Lookup_steps in HF'.
      +intros ? H'. cbn[lookup Lookup_Step_size]. destruct nth_error as [[[]| ]| ] eqn:Hnth. all:split;[ | subst F';reflexivity].
      all:revert H';intros [= ->]. now rewrite <- HF. 1-2:tspec_ext.
      +intros ? H'. cbn [lookup]. unfold Lookup_Step_steps. destruct nth_error as [[[]| ]| ] eqn:Hnth. easy.
        all:split;[ | subst F';reflexivity]. all:inv H'. all:tspec_ext.
    - destruct (nth_error H a) as [[[g' b]| ]| ] eqn:Hnth. 2-3:easy. destruct n as [ | n]. easy. intros _.
      cbn [lookup]. rewrite Hnth.
      unfold Lookup_size in HF;fold Lookup_size in HF. rewrite Hnth in HF.
      eexists (b,n,_). repeat apply conj. 
      + subst F. cbn. tspec_ext.
      + subst F'. cbn. rewrite Hnth. reflexivity.
      +intros. subst F. reflexivity.
  Qed.


  (*legacy *)
  Lemma Lookup_Realise : Lookup ⊨ Lookup_Rel.
  Proof.
    repeat (eapply RealiseIntroAll;intro). eapply Realise_monotone.
    -eapply TripleT_Realise. eapply Lookup_SpecT_space with (ss:=[| _;_;_;_;_|]).
    -cbn.  intros ? [] H **. modpon H.
    {unfold "≃≃",withSpace;cbn. intros i; destruct_fin i;cbn. all:eassumption. }
    repeat destruct _;unfold "≃≃",withSpace in H;cbn in H.
    all:destruct H as [Heq H].  
    2,3:discriminate Heq. 2:easy.
    all:specializeFin H. eexists;repeat split; easy.
  Qed.

  Definition Lookup_T : tRel sigLookup^+ 5 :=
    fun tin k =>
      exists (H: Heap) (a n: nat),
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(retr_nat_lookup_clos_ad) a /\
        tin[@Fin2] ≃(retr_nat_lookup_clos_var) n /\
        isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\
        Lookup_steps H a n <= k.

  Lemma Lookup_Terminates : projT1 Lookup ↓ Lookup_T.
  Proof.
    repeat (eapply TerminatesInIntroEx;intro). eapply TerminatesIn_monotone.
    -eapply TripleT_TerminatesIn. eapply TripleT_RemoveSpace,Lookup_SpecT_space.
    -intros ? k H **. modpon H.
    split. 2:eassumption. 
    unfold "≃≃",withSpace;cbn. intros i; destruct_fin i;cbn. all:assumption. 
  Qed.

End Lookup.


Arguments Lookup_steps : simpl never.
Arguments Lookup_size : simpl never.
