From Undecidability.L Require Import L Tactics.LTactics.

From Undecidability.L.AbstractMachines Require Import AbstractHeapMachineDef UnfoldTailRec FunctionalDefinitions.
From Undecidability.L.AbstractMachines.Computable Require Import Unfolding HeapMachine Shared.

From Undecidability.L.Datatypes Require Import Lists LBinNums.
From Undecidability.L.Functions Require Import BinNums BinNumsCompare UnboundIteration Proc.

Import AbstractHeapMachineDef.clos_notation .

Definition extractRes (sigma : state) :=
  match sigma with
    ([],[g],_) => Some (g)
  | _ => None
  end.

Definition evalForTime__step : N * state -> N * state + option (clos * list heapEntry) :=
  fun '(i,sigma) =>
    let '(_,_,H):= sigma in
    match extractRes sigma with
      Some g => inr (Some (g,H))
    | _ => if (0 <? i)%N then 
            match heapStep sigma with
              Some sigma' => inl (N.pred i,sigma')
            | _ => inr None 
            end
          else inr None
    end.


Definition init__evalForTime (fuel:N) (s:term) :=
  ((4 * fuel +1)%N,init s).

Definition evalForTime (fuel : N) ( s:term) : option (clos * list heapEntry) :=
  if closedb s then
    let '(fuel,x) := init__evalForTime fuel s in
    
    match loopSum (N.to_nat fuel + 1) evalForTime__step (fuel,x) with
      Some g => g
    |  _ => None
    end
  else None.

Lemma spec_extractRes sigma:
  match extractRes sigma with
    Some g => exists H, sigma = ([],[g],H)
  | None => forall g H, sigma <> ([],[g],H)
  end.
Proof.
  unfold extractRes.
  all:repeat (let eq := fresh "eq" in destruct _ eqn:eq).
  all:try congruence. eexists _;repeat f_equal. congruence.
Qed.

Arguments extractRes : simpl never.

Lemma spec_evalForTime__step i sigma:
  match evalForTime__step (i,sigma) with
    inl (i',sigma') => i = N.succ i' /\ step sigma sigma' /\ extractRes sigma = None
  | inr None => (i = 0%N \/ terminal step sigma) /\ extractRes sigma = None
  | inr (Some (g,H)) => sigma = ([],[g],H) 
  end.
Proof.
  specialize (heapStep_sound sigma) as R.
  specialize (spec_extractRes sigma) as H''.
  all:cbn.
  all:destruct sigma as [[T V] H];cbn [snd].
  all:destruct (N.ltb_spec0 0 i);[|replace i with (0%N) by Lia.nia].
  all:repeat (let eq := fresh "eq" in destruct _ eqn:eq).
  all:try discriminate.
  all:subst.
  all:repeat match goal with
               H :  inl _ = inl _ |- _ => inv H
             | H :  inr _ = inr _ |- _ => inv H
             end.
  1:now split;(tauto + Lia.nia).
  all:try (destruct H'' as (?&H'');inv H'').
  all:easy.
Qed.

Instance termT_extractRes : computableTime' extractRes (fun _ _ => (23,tt)).
Proof.
  unfold state.
  extract. solverec. 
Qed.

Definition time_evalForTime__step x :=
  let '(i,x) := x in
  let '(T,V,H):=x in
  match extractRes x with
    Some g  => 0
  | _ => N.size_nat i * 12
        + if (0 <? i)%N
          then heapStep_time T H
          else 0
  end + 81.

Instance termT_evalForTime__step : computableTime' evalForTime__step (fun x _ => (time_evalForTime__step x,tt)).
Proof.
  unfold state.
  extract. intros (i&((T&V)&H)). unfold time_evalForTime__step. (*recRel_prettify2.*)
  all:solverec.
Qed.

Arguments evalForTime__step : simpl never.
(*
  Lemma time_evalForTime__step_eq i T V H:
    ~(T=[] /\ exists g, V=[g]) ->
    time_evalForTime__step (i, (T, V, H))
    = N.size_nat i * 12
      + (if (0 <? i)%N then heapStep_time T H else 0)
      + 60.
  Proof.
    intros ?.
    unfold time_evalForTime__step. destruct T. destruct V as [|? []]. 2:exfalso.
    all:destruct (N.ltb_spec0 0 i);[|try easy]. all:easy.
  Qed.*)



Instance termT_init__evalForTime : computableTime' init__evalForTime (fun fuel (_:unit) => (1,fun s (_:unit) => (size s * 108 + N.size_nat fuel * 84 + 244,tt))).
Proof.
  eapply computableTimeExt with (x:=fun fuel s => ((fuel + fuel + fuel + fuel +1)%N,init s)).
  -unfold init__evalForTime. repeat intro. hnf. f_equal. Lia.nia.
  -extract.
   recRel_prettify2. reflexivity.
   change (N.size_nat 1) with 1. ring_simplify.
   
   repeat rewrite N_size_nat_add_leq.
   rewrite !Nat.max_l. all:try Lia.lia.
Qed.

Tactic Notation "destruct" "*" "eqn" :=
  let E := fresh "eq" in destruct * eqn:E.

Definition R__step := fun '(i,s) '(i',s') => i = N.succ i' /\ step s s'.

Lemma pow_Rstep k i i' x x':
  ARS.pow R__step k (i,x) (i',x')
  <-> (i = i' + N.of_nat k)%N /\ ARS.pow step k x x'.
Proof.
  induction k in i',x'|-*.
  {unfold pow. cbn. split. now intros [=]. intros. f_equal; intuition try solve [lia|easy]. }
  replace (S k) with (k + 1) in * by omega.
  rewrite !pow_add. unfold rcomp.
  repeat setoid_rewrite <- rcomp_1.
  split.
  -intros ([]&(->&?)%IHk&?&?). intuition. lia. eauto.
  -intros (->&(?&?&?)).
   eexists (_,_). rewrite IHk. cbn. repeat split. 2,3:eassumption. lia.
Qed.

Import Undecidability.L.AbstractMachines.LargestVar Undecidability.L.AbstractMachines.AbstractHeapMachine.


Lemma time_uiter_evalForTime__step s fuel:
  uiterTime evalForTime__step (fun x (_:unit) => (time_evalForTime__step x,tt)) (N.to_nat fuel + 1) (fuel,init s) <=
  (N.to_nat fuel + 1) * (N.size_nat fuel * 12 + heapStep_timeBound (largestVar s) (N.to_nat fuel) + 90).
Proof.
  rewrite uiterTime_computesRel
    with (R:= R__step)
         (t__step := N.size_nat fuel * 12 + heapStep_timeBound (largestVar s) (N.to_nat fuel) + 81)
         (t__end := 0).
  2:{
    intros fuel' (i'&x') ? R.
    eapply pow_Rstep in R as (->&R). cbn [fst].
    specialize spec_evalForTime__step with (i:=i') (sigma:=x') as H'.
    specialize (spec_extractRes x') as Hx'.
    -destruct x' as [[T V] Hp].
     cbn [fst snd] in *.
     unfold time_evalForTime__step.
     destruct extractRes.
     +destruct evalForTime__step as [[]|]. now destruct H'. split. 2:tauto. lia.
     +split.
      *rewrite N_size_nat_monotone with (n':=(i' + N.of_nat fuel')%N). 2:Lia.nia.
       destruct N.ltb_spec0 with (x:=0%N) (y:=i'%N). 2:Lia.nia.
       rewrite heapStep_timeBound_le. 2:eassumption.
       rewrite heapStep_timeBound_mono with (k':=(N.to_nat (i' + N.of_nat fuel'))). 2:Lia.nia. Lia.nia.
      *destruct evalForTime__step as [[]|]. 2:easy.
       split. 2:easy. easy.
  }
  Lia.nia.
Qed.  

Lemma sound_evalForTime__step fuel x: {res & loopSum (N.to_nat fuel +1 ) evalForTime__step (fuel,x) = Some res}.
Proof.
  remember (N.to_nat fuel) as n eqn:eqn.
  induction n in eqn,fuel,x|-*.
  all:cbn.
  all:specialize (spec_evalForTime__step fuel x) as H'.
  all:destruct evalForTime__step as [[]|].
  1:exfalso;Lia.nia.
  1,3:eauto.
  {destruct H' as (->&?&?).
   edestruct IHn with (fuel:=n0). Lia.nia.
   eauto.
  }
Qed.    

Definition term_evalForTime : term := Eval cbn [convert TH]in (λ fuel s, (!!(extT (closedb)) s) (λ _, (!!(uiter evalForTime__step) (!!(extT (init__evalForTime)) fuel s))) (λ _, (enc (None (A:=clos * list heapEntry)))) I).

Definition t__evalForTime maxVar (size:nat) fuel :=
  let fuel' := (4*fuel + 1) in
  size *139 + N.size_nat (N.of_nat fuel) * 84+
  (fuel' + 1) * (N.size_nat (N.of_nat fuel') * 12
                 + heapStep_timeBound maxVar fuel' +90) +264.

Instance evalForTime_comp : computableTime' evalForTime (fun fuel _ => (1,fun s _ => (t__evalForTime (largestVar s)(size s) (N.to_nat fuel),tt))).
Proof.
  exists term_evalForTime. unfold term_evalForTime,evalForTime.
  Intern.cstep. Intern.cstep. Intern.cstep.
  destruct closedb. 1,2:reflexivity. Unshelve.
  4:{ eapply uiter_sound. unfold evalForTime,init__evalForTime. edestruct sound_evalForTime__step as (?&eq').
      rewrite eq'. reflexivity. }
  2:exact True.
  {intros fuel _. recRel_prettify2. easy.
   all:unfold t__evalForTime. 2:lia. unfold init__evalForTime. rewrite time_uiter_evalForTime__step.
   pose (fuel':=(4*fuel + 1)%N).
   fold fuel'.
   replace (4 * N.to_nat fuel + 1) with (N.to_nat fuel') by (unfold fuel';lia).
   rewrite !Nnat.N2Nat.id. lia.
  }
Qed.

Lemma rel_evalForTime__step (x : N * state) : match evalForTime__step x with
                                            | inl y => R__step x y
                                            | inr _ => terminal R__step x
                                            end.
Proof.
  destruct x as [i x]. assert (H':=spec_evalForTime__step i x).
  destruct evalForTime__step as [[]|[[]|]].
  -destruct H' as (->&?&?).
   hnf. easy.
  -intros [i' x'] R'. destruct R' as (->&R').
   assert  (Hx:=spec_extractRes x). destruct extractRes.
   +destruct Hx as (?&->).
    inv R'.
   +easy.
  -intros [] []. destruct H' as [[->|Ter] ?]. easy.
   edestruct Ter. easy.
Qed.

Lemma sound_evalForTime__step2' i sigma g H:
  loopSum (N.to_nat i + 1) evalForTime__step (i,sigma) = Some (Some (g,H))
  <-> (exists k, k <= N.to_nat i /\ ARS.pow step k sigma ([],[g],H)).
Proof.
  split.
  -intros H'.
   eapply loopSum_rel_correct2 with (R:=R__step) in H' as (k&(x'&i')&?&eq1&R&Ter&eq2). 2:exact rel_evalForTime__step.
   eapply pow_Rstep in R as (->&R).
   eassert (H'':=spec_evalForTime__step _ _ ).
   unfold state in *.
   rewrite eq2 in H''.
   eassert (H':=spec_extractRes i').
   destruct extractRes;cbn;try congruence.
   destruct H' as (?&->). inv H''. eexists;split. 2:eauto. lia.
  -intros (k'&?&?).
   induction k' in i,sigma,k',H1,H0 |-*.
   +inv H1. replace (N.to_nat i + 1) with (1 + N.to_nat i). cbn.
    specialize (spec_evalForTime__step i ([],[g],H)). destruct evalForTime__step as [[]|[[]|]]. all:easy.
   +replace (S k') with (1+k') in H1 by easy.
    assert (H1':=H1).
    eapply pow_add in H1 as (sigma'&R&H1).
    eapply rcomp_1 in R.
    assert (exists i', N.to_nat i = S (N.to_nat i')) as (i'&eq) by (exists (i-1)%N;lia).
    rewrite eq in *. cbn.
    specialize (spec_evalForTime__step i sigma). destruct evalForTime__step as [[? sigma'']|[[]|]].
    *intros (->&?&?). replace n with i' in * by lia.
     apply IHk'. lia.
     specialize parametrized_semi_confluence with (X:=state) (t1:=([],[g],H) ) (3:=H2) (2:=H1') as (?&?&?&?&?&?&?&?);[now eauto using functional_uc,step_functional|].
     destruct x. 2:{ destruct H6 as (?&?&?);easy. }
     inv H6.
     replace k' with x0 by lia. easy.
    *intros ->. easy.
    *intros [[|Ter ]]. easy. edestruct Ter;easy.
Qed. 

Lemma evalForTime_spec (s:term) (fuel : N):
  match evalForTime fuel s with
  |Some (g,H) =>
   closed s
   /\ (exists k, k <= N.to_nat (4* fuel+1) /\ ARS.pow step k (init s) ([],[g],H))
   /\ exists t, reprC H g t /\ s ⇓(<= N.to_nat fuel) t
  | None => ~ closed s \/ ~ exists t,  s ⇓(<= N.to_nat fuel) t
  end.
Proof.
  unfold evalForTime. destruct (closedb_spec s). 2:easy.
  cbn [init__evalForTime].
  destruct loopSum as [[[]|]|] eqn:eq.
  -split. easy.
   eapply sound_evalForTime__step2' in eq. split. easy.
   destruct eq as (?&?&?).
   edestruct soundness as (?&?&?&?&eq&?&?&?). 2:split. 1,2:eassumption. now intros ? ?.
   inv eq.
   rewrite ResourceMeasures.timeBS_evalIn in H1.
   do 2 esplit. eassumption. eapply evalIn_evalLe. 2:eassumption. lia.
  -right. intros (?&(?&?&R')%evalLe_evalIn).
   rewrite <- ResourceMeasures.timeBS_evalIn in R'.
   eapply correctTime in R' as (?&?&?&?). 2:easy.
   eassert (H':=sound_evalForTime__step2' _ _ _ _). rewrite eq in H'. destruct H' as [_ H']. discriminate H'.
   repeat eexists. 2:eassumption. lia.
  -edestruct sound_evalForTime__step as (?&eq'). rewrite eq' in eq. easy.
Qed.

Lemma mono_t__evalForTime maxVar maxVar' x x' size size' :
  maxVar <= maxVar' -> x <= x' -> size <= size' -> t__evalForTime maxVar size x <= t__evalForTime maxVar' size' x'.
Proof.
  intros H1 H2 H3.
  unfold t__evalForTime.
  repeat (lazymatch goal with
            |- _ + _ <= _ + _ => eapply plus_le_compat
          | |- _ * _ <= _ * _ => eapply mult_le_compat
          | |- _ => first [eassumption | reflexivity | eapply N_size_nat_monotone | eapply unfoldBool_time_mono | Lia.nia |eapply heapStep_timeBound_mono'] 
          end).
Qed.

Lemma suplin_t__evalForTime maxVar size x : x <= t__evalForTime maxVar size x. 
Proof.
  unfold t__evalForTime. Lia.nia.
Qed.
