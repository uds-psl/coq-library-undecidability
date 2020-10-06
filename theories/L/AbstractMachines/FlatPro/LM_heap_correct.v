From Undecidability.L Require Import Util.L_facts Complexity.ResourceMeasures.
From Undecidability.L Require Import LM_heap_def.

Import Lia.
(** ** Direct correctness proof  *)

Inductive reprP : Pro -> term -> Prop :=
  reprPC s : reprP (compile s) (lam s).

(** *** Correctnes Heap-interaction *)

Definition extended (H H' : Heap) := forall alpha m, nth_error H alpha = Some m -> nth_error H' alpha = Some m.


Lemma get_current H m H' alpha : put H m = (alpha,H') -> nth_error H' alpha = Some m.
Proof.
  unfold put. intros [= <- <-].
  rewrite nth_error_app2. now rewrite <- minus_n_n. reflexivity.
Qed.

Lemma put_extends H H' m b: put H m = (b,H') -> extended H H'.
Proof.
  unfold extended,put.
  intros [= <- <-] ? ? ?. rewrite nth_error_app1;eauto using nth_error_Some_lt.
Qed.

Lemma tailRecursion_compile s P a T:
  tailRecursion (a,compile s ++ P) T = ((a,compile s ++ P))::T.
Proof.
  induction s in P,T|-*.
  all:cbn [compile].
  1,3:easy.
  rewrite <- !app_assoc. rewrite IHs1. now autorewrite with list.
Qed.


Lemma jumpTarget_correct s c: jumpTarget 0 [] (compile s ++ retT::c) = Some (compile s,c).
Proof.
  change (Some (compile s,c)) with (jumpTarget 0 ([]++compile s) (retT::c)).
  generalize 0.
  generalize (retT::c) as c'. clear c.
  generalize (@nil Tok) as c. 
  induction s;intros c' c l.
  -reflexivity.
  -cbn. autorewrite with list. rewrite IHs1,IHs2. cbn. now autorewrite with list. 
  -cbn. autorewrite with list. rewrite IHs. cbn. now autorewrite with list.
Qed.

Import L_Notations.
(** *** Unfolding *)

Inductive unfolds H a: nat -> term -> term -> Prop :=
| unfoldsUnbound k n :
    n < k ->
    unfolds H a k (var n) (var n)
| unfoldsBound k b P s s' n:
    n >= k ->
    lookup H a (n-k) = Some (b,P) ->
    reprP P s ->
    unfolds H b 0 s s' ->
    unfolds H a k (var n) s'
| unfoldsLam k s s':
    unfolds H a (S k) s s' ->
    unfolds H a k (lam s) (lam s')
| unfoldsApp k (s t s' t' : term):
    unfolds H a k s s' ->
    unfolds H a k t t' ->
    unfolds H a k (s t) (s' t').

Lemma unfolds_bound H k s s' a:
  unfolds H a k s s'
  -> bound k s'.
Proof.
  induction 1.
  -now constructor. 
  -inv H2. inv H3. constructor. inv IHunfolds. eapply bound_ge. eauto. lia.
  -now constructor.
  -now constructor. 
Qed.


Inductive reprC : Heap -> _ -> term -> Prop :=
  reprCC H P s a s' :
    reprP P s ->
    unfolds H a 0 s s' ->
    reprC H (a,P) s'.

Lemma unfolds_subst' H s s' t' a a' k g:
  nth_error (A:=HEntr) H a' = Some (Some (g,a)) ->
  reprC H g t' ->
  unfolds H a (S k) s s' ->
  unfolds H a' k s (subst s' k t').
Proof.
  intros H1 R I__s. remember (S k) as k' eqn:eq__k.
  induction I__s in H1,k,eq__k|-*. all:subst k0. 
  -cbn. destruct (Nat.eqb_spec n k).
   +assert (H':lookup H a' (n-k) = Some g).
    {subst n. cbn. rewrite Nat.sub_diag. cbn. rewrite H1. reflexivity. }
    inv R.
    decide _. 
    econstructor. all:eauto.
    econstructor. all:eauto.    
   +decide _. econstructor; eauto. lia.
    econstructor. lia.
  -rename s into u.
   assert (H':lookup H a' (n-k) = Some (b,P)).
   {destruct n. lia. rewrite Nat.sub_succ_l. cbn. rewrite H1. now rewrite Nat.sub_succ in H2. lia. }
   rewrite bound_closed_k.
   2:{ eapply bound_ge with (k:=0). 2:lia. now eauto using unfolds_bound. }
   econstructor. all:try eassumption;lia.
  -econstructor. all:eauto.
  -econstructor. all:eauto.
   Unshelve. all: repeat econstructor.
Qed.


Lemma unfolds_subst H s s' t' a a' g:
  nth_error H a' = Some (Some (g,a)) ->
  reprC H g t' ->
  unfolds H a 1 s s' ->
  unfolds H a' 0 s (subst s' 0 t').
Proof.
  apply unfolds_subst'.
Qed.


Lemma bound_unfolds_id H k s a:
  bound k s ->
  unfolds H a k s s.
Proof.
  induction 1.
  -now constructor. 
  -now constructor. 
  -now constructor. 
Qed.


Instance extended_PO :
  PreOrder extended.
Proof.
  unfold extended;split;repeat intro. all:eauto.
Qed.

Typeclasses Opaque extended.

Lemma lookup_extend H H' a x g:
  extended H H' -> lookup H a x = Some g -> lookup H' a x = Some g.
Proof.
  induction x in H,H',a,g|-*;intros H1 H2.
  all:cbn in H2|-*.
  all:destruct nth_error as [[[]|]|]eqn:H3.
  all:try congruence.
  all:try rewrite (H1 _ _ H3).
  all:try congruence.
  eapply IHx;eauto.
Qed.

Lemma unfolds_extend H H' a s t k :
  extended H H' ->
  unfolds H a k s t ->
  unfolds H' a k s t.
Proof.
  induction 2.
  all:econstructor. 1-2,4-8:now eauto. erewrite lookup_extend;eauto.
Qed.


Instance unfold_extend_Proper : Proper (extended ==> eq ==> eq ==> eq ==> eq ==>Basics.impl) unfolds.
Proof.
  repeat intro. subst. eapply unfolds_extend.  all:eassumption.
Qed.

Lemma reprC_extend H H' g s:
  extended H H' ->
  reprC H g s ->
  reprC H' g s.
Proof.
  inversion 2. subst. eauto using reprC, unfolds_extend.
Qed.


Instance reprC_extend_Proper : Proper (extended ==> eq ==> eq ==>Basics.impl) reprC.
Proof.
  repeat intro. subst. eapply reprC_extend.  all:eassumption.
Qed.

(** *** BS correctness *)

Lemma completeness' s t k s0 P a T V H:
  
  timeBS k s t -> unfolds H a 0 s0 s ->
  exists g l H', reprC H' g t
            /\ pow step l ((a,compile s0++P)::T,V,H)
                  (tailRecursion (a,P) T,g::V,H') /\ l = 3*k+1 /\ extended H H'.
Proof.
  intros Ev R.
  induction Ev in s0,P,a,T,V,H,R |-*.
  -inversion R.
   +subst k s0 s'. clear H0 R. rename P0 into Q,H3 into R,H1 into lookup_eq.
    rewrite Nat.sub_0_r in lookup_eq.
    eexists (b,Q),1,H.
    repeat split.
    *eauto using reprC.
    *cbn [compile]. rewrite <- rcomp_1. now econstructor.
    *hnf. tauto.
   +subst k s' s0. clear R. rename H3 into R.
    eexists (a,compile s1),1,H.
    repeat split.
    *eauto using reprC,reprP,unfolds.
    *cbn [compile Datatypes.app]; autorewrite with list;cbn [Datatypes.app].
     rewrite <- rcomp_1. constructor. apply jumpTarget_correct.
    *hnf. tauto.
  -inv R.
   {exfalso. inv H3. inv H4. }
   rename t0 into t1. rename H5 into I__s, H6 into I__t.
   cbn [compile List.app]; autorewrite with list; cbn [List.app].
   specialize (IHEv1 _ (compile t1 ++ appT ::P) _ T V _ I__s)
     as ([a2 P__temp]&k1&Heap1&rep1&R1&eq_k1&Ext1).
   inv rep1. inv H4. inv H6. rename H3 into I__s'.
   apply (unfolds_extend Ext1) in I__t.
   specialize (IHEv2 _ (appT ::P) _ T ((a2,compile s2)::V) _ I__t)
     as (g__t&k2&Heap2&rep2&R2&e_k2&Ext2).
   edestruct (put Heap2 (Some(g__t,a2))) as [a2' Heap2'] eqn:eq.
   assert (Ext2' := (put_extends eq)).
   apply ( reprC_extend Ext2') in rep2.
   apply ( unfolds_extend Ext2) in I__s'. apply ( unfolds_extend Ext2') in I__s'.

   specialize (unfolds_subst (get_current eq) rep2 I__s') as I__subst.
   edestruct (IHEv3 _ [] _ (tailRecursion (a,P) T) V _ I__subst) as (g__u&k3&Heap3&rep3&R3&eq_k3&Ext3).
   eexists g__u,_,Heap3.
   split;[ | split;[|split]].
   +eassumption.
   +apply pow_add. eexists. split. 
    { exact R1. }
    apply pow_add. eexists. split.
    { rewrite tailRecursion_compile. exact R2. }
    apply pow_add. eexists. split.
    { apply (rcomp_1 step). constructor;eassumption. }
    { rewrite app_nil_r in R3.  exact R3. }
   + nia.
   +rewrite Ext1,Ext2,Ext2',Ext3. reflexivity.
Qed.

Definition init s :state := ([(0,compile s)],[],[]).


Lemma completenessTime s t k:
  timeBS k s t -> closed s ->
  exists g H, reprC H g t
         /\ pow step (3*k+1) (init s)
               ([],[g],H).

Proof.
  intros H1 H2.
  edestruct (completeness' (s0:=s) (a:=0) (H:=[]) [] [] [] H1)
    as (g&?&H'&rep&R&->&_).
  -apply bound_unfolds_id. eauto using closed_k_bound.
  -autorewrite with list in R.
   exists g,H'. split. assumption.
   exact R.
Qed.

Lemma completeness s t:
  eval s t -> closed s ->
  exists g H, reprC H g t
         /\ star step (init s)
               ([],[g],H).

Proof.
  intros (n&H1%timeBS_evalIn)%eval_evalIn H2.
  edestruct completenessTime as (?&?&?&?%pow_star). 1,2:easy.
  do 3 eexists. all:easy.
Qed.

(** *** BS soundness *)

Lemma soundness' s0 s P a T V H k sigma:
  evaluatesIn step k ((a,compile s0++P)::T,V,H) sigma ->
  unfolds H a 0 s0 s ->
  exists k1 k2 g H' t n , k = k1 + k2
                     /\ pow step k1 ((a,compile s0++P)::T,V,H) (tailRecursion (a,P) T,g::V,H')
                     /\ evaluatesIn step k2 (tailRecursion (a,P) T,g::V,H') sigma
                     /\ timeBS n s t
                     /\ extended H H'
                     /\ reprC H' g t
                     /\ k1 = 3*n + 1.
Proof.
  intros [R Ter].
  unfold HClos in *.
  revert s s0 P a T V H R.
  induction k as [k IH] using lt_wf_ind .
  intros s s0 P a T V H R Unf.
  induction s0 as [|s01 IHs01 s02 IHs02 | s0] in IH,k,s,Unf,T,R,P,V,H|-*.
  -inv Unf. lia.
   assert (exists k', k = 1 + k') as (k'&->).
   {destruct k. 2:eauto. exfalso.
    inv R. eapply Ter. econstructor. rewrite Nat.sub_0_r in *. eassumption. }
   apply pow_add in R as (?&R1&R2).
   apply rcomp_1 in R1. inv R1.
   rewrite Nat.sub_0_r in *. rewrite H12 in H2. inv H2. 
   inv H3. inv H5.
   repeat esplit.
   +cbn. constructor. eassumption.
   +eassumption.
   +eauto.
   +econstructor.
   +reflexivity.
   + eauto using unfolds.
   +lia. 
  -cbn in R. inversion Unf as [| | | tmp1 tmp2 tmp3 tmp4 tmp5 Unf1 Unf2]. subst tmp1 tmp2 tmp3 s.
   rewrite <- !app_assoc in R.
   pose (R':=R).
   eapply IHs01 in R' as (k11&k12&[a' s1']&H'1&t1&n1&eq1&R11&[R12 _]&Ev1&Ext1&Rg1&eqn1). 3:eassumption.
   rewrite tailRecursion_compile in R12.
   
   (*inv Rg1. inv H6. inv H8.*)
   pose (R':=R12).
   eapply IHs02 in R' as (k21&k22&g2&H'2&t2&n2&eq2&R21&[R22 _]&Ev2&Ext2&Rg2&eqn2).
   3-4:now eauto using unfolds_extend.
   2:{ intros. eapply IH. lia. all:eauto. }
   setoid_rewrite Ext2 in Rg1.
   (*inv Rg2. *) (*inv H1. inv H2.*)
   cbn in R22.
   assert (exists k22', k22 = 1 + k22') as (k22'&->).
   {destruct k22. 2:eauto. exfalso.
    inv R22. eapply Ter. econstructor. reflexivity. }
   pose (R':=R22).
   apply pow_add in R' as (?&R2'&R3).
   apply rcomp_1 in R2'. inversion R2' as [ |  AA BB CC DD EE KK H3' b GG HH eqH'2 JJ| ]. subst AA BB CC EE GG HH DD KK. subst x.
   specialize (put_extends eqH'2) as Ext3.
   inversion Rg1 as [AA BB t1'0 CC t1' Unft']. subst AA BB CC t1.
   destruct Unft'. inversion H0 as [| | AA BB t1'' unf''' EE FF |]. subst AA BB t1'. clear H0.
   edestruct IH with (P:=@nil Tok) as (k31&k32&g3&H'3&t3&n3&eq3&R31&[R32 _]&Ev3&Ext3'&Rg3&eqn3).
   2:{ autorewrite with list. exact R3. } now nia.
   {
    eapply unfolds_subst.
    -eauto using get_current.
    -now rewrite <- Ext3.
    -eapply unfolds_extend. 2:eassumption. easy.
   }
   unfold tailRecursion at 1 in R32.
   inversion Rg2 as [AAA BBB CCC DDD EEE FFF GGG HHH III]. subst AAA g2 EEE. inversion FFF. subst BBB CCC. inversion GGG. subst t2.
   inversion Rg3 as [AA BB CC DD EE FF]. subst g3 AA EE. destruct FF. (*inv H1. inv H2. *)
   eexists (k11+(k21+(1+k31))),k32,_,_,_.
   repeat eexists.
   +lia.
   +cbn [compile]. autorewrite with list.
    rewrite app_nil_r in R31. unfold tailRecursion in R31 at 2. 
    repeat (eapply pow_add with (R:=step);eexists;split).
    *eassumption.
    *rewrite tailRecursion_compile. eassumption.
    *cbn. eapply rcomp_1 with (R:=step). constructor. eassumption.
    *eassumption.
   +eassumption.
   +eassumption.
   + econstructor. all:eauto. 
   +now rewrite Ext1,Ext2,Ext3.
   +eauto using unfolds.
   +lia. 
  -inv Unf.
   assert (exists k', k = 1 + k') as (k'&->).
   {destruct k. 2:eauto. exfalso.
    inv R. eapply Ter. cbn. econstructor. autorewrite with list. eapply jumpTarget_correct. }
   apply pow_add in R as (?&R1&R2).
   apply rcomp_1 in R1. inv R1.
   autorewrite with list in H8. cbn in H8. rewrite jumpTarget_correct in H8. inv H8.
   eexists 1,k',_,_,_.
   repeat esplit.
   +cbn. constructor. autorewrite with list. apply jumpTarget_correct.
   +eassumption.
   +eauto.
   +constructor.
   +reflexivity.
   +eauto using unfolds.
   +lia. 
Qed.

Lemma soundnessTime' s sigma k V a s0 H:
  evaluatesIn step k ([(a,compile s0)],V,H) sigma ->
  unfolds H a 0 s0 s ->
  exists g H' t n ,  pow step k ([(a,compile s0)],V,H) sigma
                    /\ sigma = ([],g::V,H')
                    /\ timeBS n s t
                    /\ extended H H'
                    /\ reprC H' g t
                    /\ k = 3*n + 1.
Proof.
  intros cs ?.
  edestruct soundness' with (P:=@nil Tok) as (k1&k2&g&H'&t&eq&R1&?&[R2 ?]&Ev&?&Rgt&->).
  all:try rewrite app_nil_r in *. 1,2:easy. 
  -cbn in R2.
    assert (k2 = 0) as ->.
   {destruct k2. eauto. exfalso.
    destruct R2 as (?&R'&?). inv R'. }
   inv R2. cbn [tailRecursion] in H1.
   eexists _,_,_. eexists. repeat eapply conj. all:eauto. now rewrite -> Nat.add_0_r.
Qed.

Lemma soundnessTime s sigma k:
  closed s -> 
  evaluatesIn step k (init s) sigma ->
  exists g H t n, sigma = ([],[g],H) /\ timeBS n s t /\ reprC H g t /\ k = 3*n+1.
Proof.
  intros cs ?.
  edestruct soundnessTime'  as (g&H'&t&n&R1&->&?&?&?&->).
  -easy. 
  -apply bound_unfolds_id. eapply closed_dcl. eassumption.
  -eexists _,_,_. all:eauto. 
Qed.

Lemma soundness s sigma:
  closed s -> 
  evaluates step (init s) sigma ->
  exists g H t, sigma = ([],[g],H) /\ eval s t /\ reprC H g t.
Proof.
  intros cs (?&H')%evalevaluates_evaluatesIn.
  apply soundnessTime in H'. destruct H' as (?&?&?&?&->&R&?&->). 2:eauto.
  do 5 eexists. 2:easy. now eapply evalIn_eval_subrelation, timeBS_evalIn.
Qed.
