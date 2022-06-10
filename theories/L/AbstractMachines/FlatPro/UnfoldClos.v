From Undecidability.L.AbstractMachines.FlatPro Require Import LM_heap_correct LM_heap_def.
From Undecidability.L.Prelim Require Import LoopSum.

Section fixH.
  Variable H : Heap.

  (* We define a function to unfold a closure, needed for the Turing machine M_unf. *)
  (* function that unfolds if unfoldable *)
  Definition unfoldTailRecStep '(stack,res) : (list (HClos*nat) * Pro) + option Pro :=
  match stack with
    | ((a,P),k)::stack =>
      match P with
        c::P =>
          match c with
            varT n =>
              if ( k <=? n)
              then
                  match lookup H a (n-k) with
                  | Some (b,Q) =>
                    inl (((b,Q),1)::(a,retT::P,S k)::stack,lamT::res)
                  | None => inr None
                  end
              else
                inl ((a,P,k)::stack,varT n::res)   
          | appT => inl ((a,P,k)::stack,appT::res)         
          | lamT => inl ((a,P,S k)::stack,lamT::res)
          | retT => inl ((a,P,pred k)::stack,retT::res)
          end
        | [] => inl (stack,res)
      end
    | [] => inr (Some res)
  end.

  (*
  Lemma unfoldTailRecStep_retT a k stack res fuel m:
    loopSum ((m+1) + fuel) unfoldTailRecStep ((a,repeat retT m,k)::stack,res)
    = loopSum fuel unfoldTailRecStep (stack,repeat retT m ++ res).
  Proof.
    induction m in k,res|-*;cbn. reflexivity. 
    rewrite app_comm_cons,repeat_cons,<- app_assoc.
    erewrite <- IHm. reflexivity.
  Qed.

  
  Lemma unfoldTailRecStep_split_stack stack fuel:
  exists fuel', forall stack' res,
  loopSum fuel unfoldTailRecStep (stack++stack',res)
  = match loopSum ((fuel-fuel') + 1) unfoldTailRecStep (stack,res) with
      | Some res' => loopSum fuel' unfoldTailRecStep (stack',rev res')
      | x => x
  end /\ fuel' <= fuel.
  Proof.
    induction fuel in stack|-*. 
    { exists 0. intros. destruct (loopSum (_ + 1)). all:now cbn. } 
    destruct stack as [ | [[a [|c P]] k] stack]. 
    - exists (S fuel). intros. rewrite Nat.sub_diag.
      remember (S fuel) as tmp. cbn. now rewrite rev_involutive.
    - specialize IHfuel with (stack:=stack) as (fuel'&IH). 
      exists fuel'. intros. specialize IH as (IH&?).
      rewrite Nat.sub_succ_l. 2:nia.
      cbn. rewrite IH. easy.
    - setoid_rewrite Nat.add_comm. cbn - ["-"].
      destruct c;cbn - ["-"].
      + destruct (Nat.leb_spec0 k n). destruct lookup as [[]|].
        * destruct (IHfuel ((h, l0, 1) :: (a, retT :: P, S k) :: stack)) as (fuel1&IH1). cbn in IH1.
          eexists (fuel1). intros. specialize IH1 as (->&?). 
          rewrite Nat.sub_succ_l. rewrite Nat.add_1_r. all:easy. 
        * destruct (IHfuel ((a, P, k) :: stack)) as (fuel1&IH1). cbn in IH1.
          eexists (fuel1). intros. specialize IH1 as (->&?).  
          rewrite Nat.sub_succ_l. rewrite Nat.add_1_r. all:easy.
        * destruct (IHfuel ((a, P, k) :: stack)) as (fuel1&IH1). cbn in IH1.
          eexists (fuel1). intros. specialize IH1 as (->&?).  
          rewrite Nat.sub_succ_l. rewrite Nat.add_1_r. all:easy. 
      + destruct (IHfuel ((a, P, k) :: stack)) as (fuel1&IH1). cbn in IH1.
        eexists (fuel1). intros. specialize IH1 as (->&?).  
        rewrite Nat.sub_succ_l. rewrite Nat.add_1_r. all:easy.
      + destruct (IHfuel ((a, P, S k) :: stack)) as (fuel1&IH1). cbn in IH1.
        eexists (fuel1). intros. specialize IH1 as (->&?).  
        rewrite Nat.sub_succ_l. rewrite Nat.add_1_r. all:easy.
      + destruct (IHfuel ((a, P, Nat.pred k) :: stack)) as (fuel1&IH1). cbn in IH1.
        eexists (fuel1). intros. specialize IH1 as (->&?).  
        rewrite Nat.sub_succ_l. rewrite Nat.add_1_r. all:easy.   
  Qed.

(*
Lemma unfoldTailRecStep_splita a k s P stack res fuel:
  loopSum fuel unfoldTailRecStep ((a,compile s++P,k)::stack,res)
  = loopSum fuel unfoldTailRecStep ((a,compile s,k)::(a,P,k)::stack,res).
Proof.
  induction fuel in s,stack,res,P|-*. reflexivity.
  destruct s;cbn.
  - destruct (Nat.leb_spec0 k n). destruct lookup as [[]|].
  - eexists (1). cbn [loopSum unfoldTailRecStep plus compile]. cbn. 
    destruct (Nat.leb_spec0 k n). now lia. easy.
    (*erewrite unfoldTailRecStep_retT. easy.*)
  - inv H2. edestruct IHunfolds with (fuel := S (fuel)) as (n'&eq1&?).
    rewrite Nat.add_succ_r in eq1. 
  induction s in P,k,a,stack|-*.
  all:cbn.  
Qed.*)
  *)
  Lemma unfoldTailRecStep_complete' a k s P s' stack res fuel:
    unfolds H a k s s' ->
    exists n, 
    loopSum (n + fuel) unfoldTailRecStep  ((a,compile s++P,k)::stack,res)
    = loopSum fuel unfoldTailRecStep ((a,P,k)::stack,rev (compile s')++res) /\ n <= L_facts.size s' *3.
  Proof.
    induction 1 in fuel,stack,res,P|-* using unfolds_ind'.
    - eexists (1). cbn [loopSum unfoldTailRecStep plus compile]. cbn. 
      destruct (Nat.leb_spec0 k n). now lia. easy.
      (*erewrite unfoldTailRecStep_retT. easy.*)
    - subst P0.
      edestruct (IHunfolds []) with (fuel := S (fuel +1)) as (n'&eq1&?).
      erewrite app_nil_r in eq1. cbn in eq1.
      eexists (S (n' + 2)). cbn.
      destruct (Nat.leb_spec0 k n). 2:now lia.
      rewrite H1. cbn.  
      replace (n' + 2 + fuel) with (n' + S (fuel + 1)) by nia.
      rewrite eq1. replace (fuel +1) with (S fuel) by nia. cbn.
      repeat (autorewrite with list;cbn). easy.
    - cbn. 
      edestruct (IHunfolds (retT :: P)) with (fuel := S fuel) as (n'&eq1&?).
      cbn in eq1.
      repeat (autorewrite with list;cbn).
      rewrite <- eq1.
      exists (S n' + 1). cbn. now rewrite <- Nat.add_assoc.  
    - cbn. rewrite <- !app_assoc.  
      specialize (IHunfolds2 ([appT] ++ P)) as (n2&IH2&?).  
      specialize (IHunfolds1 (compile t ++ [appT] ++ P)) as (n1&IH1&?).
      eexists (n1+n2+1). rewrite <- !Nat.add_assoc.
      rewrite IH1,IH2. cbn. 
      repeat (autorewrite with list;cbn). easy.
  Qed.

  Lemma unfoldTailRecStep_complete a k s s' n:
    unfolds H a k s s' ->
    L_facts.size s' * 3 + 2 <= n ->
    loopSum n unfoldTailRecStep ([(a,(compile s),k)],[])
    = Some (Some (rev (compile s'))).
  Proof.
    intros ? ?.
    edestruct unfoldTailRecStep_complete' with (P:=@nil Tok) as (n'&eq1&?). eassumption.
    rewrite app_nil_r in eq1.
    eapply loopSum_mono with (n:=n'+2). now Lia.nia.
    rewrite eq1. cbn. now rewrite  app_nil_r.
  Qed.

  (*
  Lemma unfoldTailRecStep_sound' P a k stack acc res fuel:
    loopSum fuel unfoldTailRecStep ((a,P,k)::stack,acc) = Some (Some res)
    -> exists s s' fuel',
                  P = compile s
                  /\ unfolds H a k s s'
                  /\ loopSum fuel unfoldTailRecStep ((a,P,k)::stack,acc)
                    = loopSum fuel' unfoldTailRecStep (stack,rev (compile s')++acc)
                  /\ fuel' <= fuel.
  Proof.
    revert P a k stack acc res.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros ? ? ? ? ? ?.
    destruct fuel. easy.
    destruct P as [|[] P].
    all:cbn in *.
    -destruct (Nat.leb_spec0 k n) as [ |n0].
    destruct lookup as [[R0 b]| ] eqn:eq__lookup . 2:now congruence.
    +intros H'.
      specialize IH with (2:=H') as (s'&fuel'&R&eq'&leq'). easy.
      rewrite eq' in *.
      destruct fuel' as [ |fuel']. easy.
      cbn in *.
      exists (lam s'), fuel'.
      repeat apply conj.
      1-2:now eauto using unfolds.
      Lia.nia.
    +intros H'.
      do 2 eexists. repeat apply conj.
      2,1:now eauto 10 using unfolds,not_ge.
      Lia.nia.
    -intros H'.
    assert (IH':=IH).
    specialize IH' with (2:=H') as (s1'&fuel1&R1&eq1&leq1). easy.
    rewrite eq1 in *.
    specialize IH with (2:=H') as (s2'&fuel2&R2&eq2&leq2). easy.
    rewrite eq2 in *.
    destruct fuel2 as [ |fuel2]. easy.
    cbn in *.
    eexists _,_. repeat apply conj.
    1,2:now eauto using unfolds.
    Lia.nia.
    -intros H'.
    specialize IH with (2:=H') as (s'&fuel'&R&eq1&leq'). easy.
    rewrite eq1 in *.
    destruct fuel' as [ |fuel']. easy.
    eexists _,_. repeat apply conj.
    1,2:now eauto using unfolds.
    Lia.nia.
  Qed.
    
  Lemma unfoldTailRecStep_sound s a k H s' fuel:
    loopSum fuel unfoldTailRecStep ([closT (s,a) k],H,[]) = Some (Some s')
    -> unfolds H a k s s'.
  Proof.
    intros H'.
    specialize (unfoldTailRecStep_sound' H') as (k0&fuel'&R&eq'&leq').
    rewrite eq' in *. destruct fuel'. easy.
    inv H'. easy.
  Qed.

  Definition largestVarState : (list task * list heapEntry * list term) -> nat :=
    fun '(stack,H,res) => max (maxl (map (fun (t:task) =>
                                        match t with
                                          closT q _ => largestVarC q
                                        | _ => 0
                                        end) stack))
                          (max (largestVarH H) (maxl (map largestVar res))).

  Lemma unfoldTailRecStep_largestVar_inv x:
    match unfoldTailRecStep x with
      inl x' => largestVarState x'
    | inr (Some A)  => largestVar A
    | _ => 0
    end
    <= largestVarState x.

  Proof.
    unfold unfoldTailRecStep.
    repeat (let eq := fresh "eq" in destruct _ eqn:eq);inv eq;try congruence.
    

    
    all:repeat match goal with
                H : _ <=? _ = true |- _ => apply Nat.leb_le in H
              | H : _ <=? _ = false |- _ => apply Nat.leb_gt in H
              | H : lookup _ _ _ = Some _ |- _ => apply lookup_size in H;cbn in H

              end.
    all:unfold largestVarState,largestVarCs,largestVarC in *; cbn;fold maxl.
    all:try Lia.lia.
  Qed. 

  Require Import Undecidability.L.Functions.Equality.



  Definition unfoldBoolean H (p:clos) : option bool :=
    let '(s,a) := p in
    match loopSum 7 unfoldTailRecStep ([closT p 1],H,[]) with
    | Some (Some t) =>
      if term_eqb (lam t) (enc true)
      then Some true
      else if term_eqb (lam t) (enc false )
          then Some false
          else None       
    | _ => None
    end.

  Lemma unfoldBoolean_complete H p (b:bool) :
    reprC H p (enc b) -> unfoldBoolean H p = Some b.
  Proof.
    intros H1. inv H1. unfold unfoldBoolean.
    erewrite unfoldTailRecStep_complete. 2:easy. 2:{ destruct b;inv H2;cbn;Lia.lia. }
    destruct b;inv H2;cbv. all:reflexivity.
  Qed.

  Lemma unfoldBoolean_sound (H : list heapEntry) (p : clos) (b : bool) :
    unfoldBoolean H p = Some b -> reprC H p (enc b).
  Proof.
    unfold unfoldBoolean.
    destruct p as [P a]. 
    destruct loopSum as [[]| ] eqn:H'. 2-3:easy.
    eapply unfoldTailRecStep_sound in H'.
    destruct (term_eqb_spec (lam t) (enc true)).
    2: destruct (term_eqb_spec (lam t) (enc false)).
    all:inversion 1. all:inv e. all:cbv in *. all:easy.
  Qed.

  *)

End fixH.