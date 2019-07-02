From Undecidability.L Require Import L Prelim.LoopSum Functions.UnboundIteration AbstractMachines.LargestVar.
From Undecidability.L.AbstractMachines Require Import AbstractHeapMachine UnfoldHeap.
Import AbstractHeapMachineDef.clos_notation.

Local Inductive task := closT (q:clos) (k:nat) | appT | lamT.

(* function that unfolds if unfoldable *)
Definition unfoldTailRecStep '(stack,H,res) : (list task * list heapEntry * list term) + option term :=
  match stack with
  | [] => match res with
           [s] => inr (Some s)
         | _ => inr None
         end
  | t::stack =>
    match t with
    | closT (s,a) k =>
      match s with
        var n => if ( k <=? n) then
                  match lookup H a (n-k) with
                  | Some q' =>
                    inl (closT q' 1::lamT::stack,H,res)
                  | None => inr None
                  end
                else
                  inl (stack,H,var n::res)
                      
      | lam s => inl (closT (s,a) (S k)::lamT::stack,H,res)
      | app s1 s2 => inl (closT (s1,a) k::closT (s2,a) k::appT::stack,H,res)
      end
    | appT => match res with
               s2::s1::res => inl (stack,H,app s1 s2::res)
             | _ => inr None
             end
    | lamT => match res with
               s::res => inl (stack,H,lam s::res)
             | _ => inr None
             end
    end
  end.

Lemma unfoldTailRecStep_complete' H a k s s' stack res fuel:
  unfolds H a k s s' ->
  exists n, 
  loopSum (n + fuel) unfoldTailRecStep (closT (s,a) k::stack,H,res)
  = loopSum fuel unfoldTailRecStep (stack,H,s'::res) /\ n <= size s' *2.
Proof.
  induction 1 in fuel,stack,res|-*.
  -eexists 1. cbn [loopSum unfoldTailRecStep plus depth]. 
   destruct (Nat.leb_spec0 k n). now omega.
   intuition.
  -edestruct IHunfolds as (n'&eq1&?).
   exists (S (n' + 1)). cbn.
   destruct (Nat.leb_spec0 k n). 2:now omega.
   rewrite H1,<- Nat.add_assoc,eq1.
   cbn. intuition.
  -edestruct IHunfolds as (n'&eq1&?).
   exists (S (n' + 1)). cbn.
   rewrite <- Nat.add_assoc,eq1. 
   cbn. intuition.
  -edestruct IHunfolds2 as (n2&eq2&?).
   edestruct IHunfolds1 as (n1&eq1&?).
   exists (S (n1 + (n2 + 1))). cbn.
   rewrite <- !Nat.add_assoc.
   rewrite eq1, eq2. 
   cbn. intuition.
Qed.

Lemma unfoldTailRecStep_complete H a k s s' n:
  unfolds H a k s s' ->
  2 * size s' + 1 <= n ->
  loopSum n unfoldTailRecStep ([closT (s,a) k],H,[])
  = Some (Some s').
Proof.
  intros ? ?.
  edestruct unfoldTailRecStep_complete' as (n'&eq1&?). eassumption.
  eapply loopSum_mono with (n:=n'+1). now Lia.nia.
  rewrite eq1. reflexivity.
Qed.

Lemma unfoldTailRecStep_sound' s a k stack H res s0 fuel :
  loopSum fuel unfoldTailRecStep (closT (s,a) k::stack,H,res) = Some (Some s0)
  -> exists s' fuel', unfolds H a k s s'
                /\ loopSum fuel unfoldTailRecStep (closT (s,a) k::stack,H,res)
                  = loopSum fuel' unfoldTailRecStep (stack,H,s'::res)
                /\ fuel' <= fuel.
Proof.
  revert s0 s a k stack res.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros ? ? ? ? ? ?.
  destruct fuel. easy.
  destruct s as [n|s1 s2|s].
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
