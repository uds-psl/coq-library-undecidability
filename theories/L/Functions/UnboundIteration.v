From Undecidability.L Require Import Tactics.LTactics Datatypes.LSum Datatypes.LOptions.
From Undecidability.L Require Export Prelim.LoopSum.

Section uiter.
  Variable X Y : Type.
  Context `{registered X}.
  Context `{registered Y}.

  Variable f : X -> X + Y.

  Variable fT : timeComplexity (X -> X + Y).
  Context `{computableTime' f fT}.

  Import HOAS_Notations.
  Definition uiter := Eval cbn -[enc] in rho (λ uiter x, !!(extT f) x (λ x' _ , uiter x') (λ y _ , y) !!I).
  
  Lemma uiter_proc : proc uiter.
  Proof. unfold uiter. Lproc. Qed.
  Hint Resolve uiter_proc : LProc.

  Fixpoint uiterTime n x :=
    match n with
      0 => 0
    | S n' => fst (fT x tt) + 9 + match f x with
                                       inl x' => uiterTime n' x'
                                     | _ => 0
                                     end
    end. 

  Lemma uiter_sound n x y:
    loopSum n f x = Some y -> evalLe (uiterTime n x) (app uiter (enc x)) (enc y).
  Proof.
    unfold uiter. Intern.recRem P.
    induction n in x|-*;intros Heq. now easy.
    cbn in Heq|-*.
    eapply (@le_evalLe_proper (match f x with inl x' => _ | _ => _ end)).
    2,3:reflexivity.
    2:{
      destruct (f x) eqn:eqfx.
      -Intern.recStepUnnamed. Lrewrite_new. rewrite eqfx. Lrewrite_new. eapply IHn. eauto.
      -inv Heq. Intern.recStepUnnamed. Lrewrite_new. rewrite eqfx. Lrewrite_new. Lreflexivity.
    }
    destruct (f x).
    all:solverec.
  Qed.

  
  Lemma uiter_total_instanceTime {Z} `{registered Z} (f':  Z -> Y) (preprocess : Z -> X) preprocessT (fuel : Z -> nat)
    `{computableTime' preprocess preprocessT} :
    (forall x, loopSum (fuel x) f (preprocess x) = Some (f' x)) ->
    computesTime (TyArr _ _) f' (λ x, !!uiter !!(L.app (extT preprocess) x)) (fun z _ => (1 + fst (preprocessT z tt) + uiterTime (fuel z) (preprocess z),tt)).
  Proof.
    cbn [convert TH].
    intros total.
    eapply computesTimeTyArr_helper with (time:=(fun x _ => _)).
    { unfold uiter. now Lproc. }
    intros z []. cbn. split. now reflexivity.
    intros ? ->.
    eexists. split. 2:reflexivity.
    eapply le_evalLe_proper. 2-3:reflexivity.
    2:{ eapply evalLe_trans with (t := (L.app uiter (enc (preprocess z)))).
        -now Lsimpl.
        -eapply uiter_sound. apply total. }
    lia.
  Qed.
    

  Lemma uiterTime_bound_onlyByN (P: nat -> _ -> Prop) boundL boundR n0 x0:
    (forall n x, n < n0
            -> P n x
            -> match f x with
              | inl x' => P (S n) x' /\ fst (fT x tt) <= boundL
              | inr y => forall n', n <= n' -> fst (fT x tt) <= boundL + boundR n'
              end) ->
    P 0 x0 -> 
    uiterTime n0 x0 <= n0 * (boundL + 9) + boundR n0.
  Proof.
    intros H'.
    pose (n0':=n0). assert (Hleq : n0<=n0') by (cbn;lia).
    replace 0 with (n0'-n0) at 1 by (cbn;lia).
    change (boundR n0) with (boundR n0').
    change n0 with n0' in H'.
    clearbody n0'.
    induction n0 in x0,Hleq |-*. 1:cbn;Lia.nia.
    intros HPx.
    cbn -[plus].
    specialize H' with (x:=x0).
    destruct (f x0).
    -edestruct H' as [? ->]. 2:eassumption. lia. rewrite IHn0. 2:easy.
     now Lia.lia.
     replace (n0'-n0) with (S (n0'-S n0)) by Lia.nia. eapply H2. 
    -rewrite H' with (n:=n0'-S n0) (n':=n0'). all:try now Lia.lia. eassumption.
  Qed.

  Lemma uiterTime_bound_recRel2 (P: nat -> _ -> Prop) (iterT : X -> nat):
    (forall i x, P i x -> match f x with
                    | inl x' => P (S i) x' /\ iterT x' + 9 + fst (fT x tt) <= iterT x
                    | inr y => fst (fT x tt) + 9 <= iterT x
                    end) ->
    forall n x,
      P 0 x -> 
      uiterTime n x <= iterT x.
  Proof.
    intros H' n x.
    pose (n':=n). assert (Hleq : n<=n') by (cbn;lia).
    replace 0 with (n'-n) at 1 by (cbn;lia).
    clearbody n'.
    induction n in x,Hleq |-*. 1:cbn;Lia.nia.
    intros HPx.
    cbn -[plus].
    specialize H' with (x:=x).
    destruct (f x) as [x'|y] eqn:eq. 
    -edestruct H' as [? H'']. eassumption. rewrite IHn.
2:easy. 2:{ replace (n'-n) with (S (n'-S n)) by Lia.nia. eassumption. }  Lia.lia.
    -cbn. rewrite <- H'. 2:easy. all:Lia.lia.
  Qed.

  Lemma uiterTime_bound_recRel (P: nat -> _ -> Prop) (iterT : nat -> X -> nat) n:
    (forall i x, P i x -> match f x with
                    | inl x' => P (S i) x' /\ iterT (n-i-1) x' + 9 + fst (fT x tt) <= iterT (n-i) x
                    | inr y => fst (fT x tt) + 9 <= iterT (n-i) x
                    end) ->
    forall x k,
      k <= n ->
      P (n-k) x -> 
      uiterTime k x <= iterT k x.
  Proof.
    intros H' x k.
    induction k in x |-*.
    1:now cbn;Lia.nia.
    intros ? HPx.
    cbn -[plus].
    specialize H' with (x:=x).
    destruct (f x) as [x'|y] eqn:eq. 
    -edestruct H' as [? H'']. eassumption. rewrite IHk.
     +replace (n - (n - (S k))) with (1+k)  in H'' by Lia.lia.
      cbn in H''. rewrite Nat.sub_0_r in H''.
      Lia.nia.
     +easy.
     +replace (n-k) with (S (n-S k)) by Lia.nia. eassumption.
    -replace (S k) with (n - (n - S k)) by Lia.lia.
     rewrite <- H'. all:easy. 
  Qed.
  
  Lemma uiterTime_computesRel (R : X -> X -> Prop) x0 k0 (t__step t__end : nat):
    (forall k' x, k' < k0 -> pow R k' x0 x ->
             fst (fT x tt) <= t__step +  match f x with
                                       | inr _ => t__end | _ => 0
                                       end
             /\  match f x with
                | inl x' =>  R x x'
                | _ => True
                end) ->
    uiterTime k0 x0 <= k0 * (t__step + 9) + t__end.
  Proof.
    intros H'.
    rewrite uiterTime_bound_onlyByN
      with (P:= fun n x =>pow R n x0 x)
           (boundL := t__step)
           (boundR := fun _ => t__end).
    -Lia.lia.
    -intros n x lt'' R'.
     specialize H' with (1:=lt'') (2:=R') as [H' H''].
     destruct (f x).
     +split. 2:easy. 
      replace (S n) with (n+1) by lia.
      eapply pow_add. eexists x. split. eauto. apply rcomp_1 with (R:=R). tauto.
     +intro. lia.
    -reflexivity. 
  Qed.  
    

End uiter.

Hint Resolve uiter_proc : LProc.
Arguments uiter _ _ _ _ _ _ _ : clear implicits.
Arguments uiter {X Y H H0} f {fT H1}.

