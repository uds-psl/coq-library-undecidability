From Undecidability.L Require Import L  Complexity.ResourceMeasures AbstractMachines.LargestVar.
From Undecidability.L Require Export AbstractMachines.AbstractHeapMachineDef.
Import AbstractHeapMachineDef.clos_notation.

Require Import Lia.

Lemma get_current H m H' alpha : put H m = (H', alpha) -> get H' alpha = Some m.
Proof.
  unfold put, get. intros [= <- <-].
  rewrite nth_error_app2. now rewrite <- minus_n_n. reflexivity.
Qed.

Lemma put_extends H H' m b: put H m = (H',b) -> extended H H'.
Proof.
  unfold extended,get,put.
  intros [= <- <-] ? ? ?. rewrite nth_error_app1;eauto using nth_error_Some_lt.
Qed.

Lemma step_functional : functional step.
Proof.
  intros ? ? ? R1 R2;inv R1;inv R2. all:congruence.
Qed.

Lemma unfolds_functional H a k:
  functional (unfolds H a k).
Proof.
  intros x y1 y2 R1 R2.
  induction R1 in y2,R2|-*.
  -inv R2. easy. nia.
  -inv R2. nia. 
   rewrite H1 in H4. inv H4.
   f_equal.
   eapply IHR1. eauto. 
  -inv R2. f_equal.
   eapply IHR1. easy.
  -inv R2. f_equal. all: now auto.
Qed.

Lemma unfolds_bound H k s s' a:
  unfolds H a k s s'
  -> bound k s'.
Proof.
  induction 1.
  -now constructor. 
  -econstructor. eapply bound_ge;eauto. omega.
  -now constructor.
  -now constructor. 
Qed.


Lemma reprC_functional H :
  functional (reprC H ).
Proof.
  intros x y1 y2 R1 R2.
  inv R1. inv R2.
  f_equal.
  eapply unfolds_functional. all:now eauto.
Qed.

Lemma unfolds_subst' H s s' t' a a' k g:
  get H a' = Some (heapEntryC g a) ->
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
    econstructor.
    all:try eauto using unfolds;try omega. 
   +econstructor. omega.      
  -rename s into u.
   assert (H':lookup H a' (n-k) = Some (u,b)).
   {destruct n. omega. rewrite Nat.sub_succ_l. cbn. rewrite H1. now rewrite Nat.sub_succ in H2. omega. }
   rewrite bound_closed_k.
   2:{ eapply bound_ge with (k:=0). 2:omega. now eauto using unfolds,unfolds_bound. }
   econstructor. all:try eassumption;omega.
  -econstructor. all:eauto.
  -econstructor. all:eauto.
Qed.


Lemma unfolds_subst H s s' t' a a' g:
  get H a' = Some (heapEntryC g a) ->
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
  all:destruct get as [[]|]eqn:H3.
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

Lemma In_extend H H' g:
  extended H H' ->
  g el H ->
  g el H'.
Proof.
  unfold extended,get.
  intros H1 H2.
  eapply In_nth_error in H2 as (?&H2).
  apply H1 in H2. eauto using nth_error_In.
Qed.

Instance reprC_extend_Proper : Proper (extended ==> eq ==> eq ==>Basics.impl) reprC.
Proof.
  repeat intro. subst. eapply reprC_extend.  all:eassumption.
Qed.

(** *** Time *)

Lemma correctTime' s t k s0 a T V H:
  timeBS k s t -> unfolds H a 0 s0 s ->
  exists g l H', reprC H' g t
            /\ pow step l (closT(s0,a)::T,V,H)
                  (T,g::V,H') /\ l = 4*k+1 /\ extended H H'.
Proof.
  intros Ev R.
  induction Ev in s0,a,T,V,H,R |-*.
  -inversion R.
   +subst k s' s0. clear H1 R. rename H5 into R.
    rewrite Nat.sub_0_r in H2.
    eexists (s1 , b),1,H.
    repeat split.
    *eauto using reprC.
    *apply (rcomp_1 step).  now constructor. 
    *hnf. tauto.
   +subst k s' s0. clear R. rename H3 into R.
    eexists (s1 , a),1,H.
    repeat split.
    *eauto.
    *apply (rcomp_1 step). constructor.
    *reflexivity.
  -inv R. 
   rename t0 into t1. rename H5 into I__s, H6 into I__t.
   specialize (IHEv1 _ _ (closT (t1,a)::appT::T) V _ I__s)
     as ((s0'&a')&k1&Heap1&rep1&R1&eq_k1&Ext1).
   inv rep1. rename H3 into I__s'.
   apply (unfolds_extend Ext1) in I__t.
   specialize (IHEv2 _ _ (appT::T) ((s0',a')::V) _ I__t)
     as (g__t&k2&Heap2&rep2&R2&eq2&Ext2).
   edestruct (put Heap2 (heapEntryC g__t a')) as [Heap2' a2'] eqn:eq.
   assert (Ext2' := (put_extends eq)).
   apply ( reprC_extend Ext2') in rep2.
   apply ( unfolds_extend Ext2) in I__s'. apply ( unfolds_extend Ext2') in I__s'.

   specialize (unfolds_subst (get_current eq) rep2 I__s') as I__subst.
   edestruct (IHEv3 _ _ T V _ I__subst) as (g__u&k3&Heap3&rep3&R3&eq3&Ext3).
   eexists g__u,(1+ (_+(k2+(1+k3)))),Heap3. 
   split;[ | split;[| split]].
   +eassumption.
   +apply pow_add. eexists. split.
    { apply (rcomp_1 step). constructor;eassumption. }
    apply pow_add. eexists. split.
    { exact R1. }
    apply pow_add. eexists. split.
    { exact R2. }
    apply pow_add. eexists. split.
    { apply (rcomp_1 step). constructor;eassumption. }
    {exact R3. }
   +lia.
   +rewrite Ext1,Ext2,Ext2',Ext3. reflexivity.
Qed.



Lemma correctTime s t k:
  timeBS k s t -> closed s ->
  exists g H, reprC H g t
         /\ pow step (4*k+1) (init s)
               ([],[g],H).

Proof.
  intros H1 H2.
  edestruct (correctTime' (s0:=s) (a:=0) (H:=[]) [] [] H1)
    as (g&l&H'&rep&R&eq&_).
  -apply bound_unfolds_id. eauto using closed_k_bound.
  -autorewrite with list in R.
   exists g,H'. split. assumption. subst l.
   eassumption.
Qed.

(** *** Soundness  *)
Definition evaluatesIn (X : Type) (R : X -> X -> Prop) n (x y : X) := pow R n x y /\ terminal R y.

Lemma soundness' s0 s a T V H k sigma:
  evaluatesIn step k (closT(s0,a)::T,V,H) sigma ->
  unfolds H a 0 s0 s ->
  exists k1 k2 g H' t n, k = k1 + k2
                    /\ pow step k1 (closT(s0,a)::T,V,H) (T,g::V,H')
                    /\ evaluatesIn step k2 (T,g::V,H') sigma
                    /\ ResourceMeasures.timeBS n s t
                    /\ extended H H'
                    /\ reprC H' g t
                    /\ k1 = 4*n+1.
Proof.
  intros [R Ter].
  revert s s0 a T V H R.
  induction k as [k IH] using lt_wf_ind .
  intros s s0 a T V H R Unf.
  assert (exists k', k = 1 + k') as (k'&->).
  {destruct k. 2:easy.
   exfalso. inv R. inv Unf.
   1:easy.
   all:eapply Ter.
   1:rewrite Nat.sub_0_r in H1.
   all:eauto using step.
  }
  apply pow_add in R as (?&R0&R).
  apply rcomp_1 in R0.
  inv R0.
  -inv Unf. eexists 1,k',_,_,_,0.
   repeat eapply conj.
   2:apply rcomp_1 with (R:=step).
   3:{ exact R. }
   6:{ now econstructor. }
   all:try easy;eauto using timeBS,step.
   
  -inv Unf. easy.
   rewrite Nat.sub_0_r in H2.
   rewrite H2 in H7. inv H7.
   
   eexists 1,k',_,_,_,0.
   repeat eapply conj.
   2:apply rcomp_1 with (R:=step).
   3:{ exact R. }
   6:{ now econstructor. }
   all:try easy;eauto using timeBS,step.
  -inversion Unf as [| | | tmp1 tmp2 tmp3 tmp4 tmp5 Unf1 Unf2]. subst tmp1 tmp2 tmp3 s.
   edestruct IH with (2:=R) (3:=Unf1) as (k11&k12&[s1' a']&H'1&t1&n1&eq1&R11&[R12 _]&Ev1&Ext1&Rg1&eqn1). now omega.
   rewrite Ext1 in Unf2.
   edestruct IH with (2:=R12) (3:=Unf2) as (k21&k22&g2&H'2&t2&n2&eq2&R21&[R22 _]&Ev2&Ext2&Rg2&eqn2). now omega.
   setoid_rewrite Ext2 in Rg1.
   
   assert (exists k22', k22 = 1 + k22') as (k22'&->).
   {destruct k22. 2:eauto. exfalso.
    inv R22. eapply Ter. econstructor. reflexivity.
   }
   apply pow_add with (R:= step) in R22 as (x&R22&R3).
   apply rcomp_1 in R22. inversion R22 as [|  AA BB CC DD H3 b GG HH | |]. subst AA BB CC GG HH DD. subst x.
   assert (Ext2':=put_extends H0).
   inversion Rg1 as [AA BB CC t1' Unft']. subst AA BB CC t1.
   edestruct IH with (2:=R3) as (k31&k32&g3&H'3&t3&n3&eq3&R31&[R32 _]&Ev3&Ext3&Rg3&eqn3).
   1:now omega.
   1:{ eapply unfolds_subst. now eauto using get_current.
       all:setoid_rewrite <- Ext2'. all:eauto.
   }
   eexists (1+(k11+(k21+(1+k31)))),k32,_,_,_,_.
   repeat eapply ex_intro. repeat eapply conj.
   +omega.
   +repeat (eapply pow_add with (R:=step);eexists;split).
    all:try eapply rcomp_1 with (R:=step).
    all:now eauto using step.
   +eassumption.
   +eauto.
   +inv Rg1. inv Rg2. inv Rg3. econstructor.
    all:try eassumption. reflexivity.
   +setoid_rewrite Ext1. setoid_rewrite Ext2. setoid_rewrite Ext2'. easy.
   +eassumption.
   +omega.
Qed.

Lemma soundness k s sigma:
  closed s -> 
  evaluatesIn step k (init s) sigma ->
  exists g H t n , sigma = ([],[g],H) /\ ResourceMeasures.timeBS n s t /\ reprC H g t /\ k = 4*n+1.
Proof.
  intros cs [R Ter].
  edestruct soundness' as (k1&k2&g&H&t&n&eq&R1&[R2 _]&Ev&_&Rgt&->).
  -split. all:eassumption.
  -apply bound_unfolds_id. eapply closed_dcl. eassumption.
  -assert (k2 = 0) as ->.
   {destruct k2 as [|]. easy.
    destruct R2 as (?&R'&R2). inv R'.
   }
   inv R2.
   eauto 10.
Qed.

Lemma lookup_el H alpha x e: lookup H alpha x = Some e -> exists beta, heapEntryC e beta el H.
Proof.
  induction x in alpha, e|-*.
  all:cbn. all:unfold get. all:destruct nth_error as [[]|] eqn:eq.
  all:intros [= eq'].
  1:subst.
  all:eauto using nth_error_In.
Qed.


Lemma lookup_size H a n q: lookup H a n = Some q -> largestVarC q <= largestVarH H.
Proof.
  intros (b&?)%lookup_el.
  eapply maxl_leq. eapply in_map_iff. eexists (heapEntryC _ _). eauto.
Qed.


Lemma largestVarH_bound H c:
  (forall q beta, heapEntryC q beta el H -> largestVarC q <= c) -> largestVarH H <= c.
Proof.
  intros H'. eapply maxl_leq_l. setoid_rewrite in_map_iff.
  intros ? ([]&<-&?). eauto.
Qed.


Inductive subterm (s:term) : term -> Prop :=
  subtermR : subterm s s
| subtermAppL (s' t:term) : subterm s s' -> subterm s (s' t)
| subtermAppR (t s':term) : subterm s s' -> subterm s (t s')
| subtermLam s': subterm s s' -> subterm s (lam s').

Instance subtermPO : PreOrder subterm.
Proof.
  split. now constructor.
  intros x y z H1 H2.
  induction H2 in H1,x|-*. all:eauto using subterm.
Qed.

Lemma subterm_lam_inv s s0 :
  subterm (lam s) s0 -> subterm s s0.
Proof.
  intros.  rewrite <- H. eauto using subterm.
Qed.

Lemma subterm_app_l s t s0 :
  subterm (app s t) s0 -> subterm s s0.
Proof.
  intros. rewrite <- H. eauto using subterm.
Qed.

Lemma subterm_app_r s t s0 :
  subterm (app s t) s0 -> subterm t s0.
Proof.
  intros. rewrite <- H. eauto using subterm.
Qed.

Lemma subterm_largestVar s s' :
  subterm s s' -> largestVar s <= largestVar s'.
Proof.
  induction 1;cbn;Lia.nia.
Qed.

Section Analysis.

  Variable s0 : term.
  (* Hypothesis cs : closed s.*)
  Variable T : list task.
  Variable V : list clos.
  Variable H: list heapEntry.
  Variable i : nat.

  Hypothesis R: pow step i (init s0) (T,V,H).

  Lemma subterm_property:
    (forall s a, closT (s,a) el T -> subterm s s0)
    /\ (forall s a, (s,a) el V -> subterm (lam s) s0)
    /\ (forall s a b, heapEntryC (s,a) b el H -> subterm (lam s) s0).
  Proof.
    induction i in R,T,V,H|-*.
    {inv R. cbn. intuition. inv H0. eauto using subterm. }
    replace (S n) with (n + 1) in R by omega.
    apply pow_add with (R:=step) in R. destruct R as [[[T' V'] H'] [R1 R2]].
    specialize IHn with (1:=R1) as (IH__T&IH__V&IH__H).
    eapply rcomp_1 in R2.
    inv R2.
    all:cbn in *.
    all:(repeat split;repeat intro;
         repeat lazymatch goal with
                | H : (_,_)=(_,_) |- _ => inv H
                | H : heapEntryC _ _=heapEntryC _ _ |- _ => inv H
                | H : closT _ = closT _ |- _ => inv H
                | H : _ \/ _ |- _=> inv H
                | H : lookup H _ _ = Some _ |- _=> eapply lookup_el in H as (?&?)
                | H : appT = closT _ |- _ => inv H
                | H : put _ _ = (_, _) |- _ =>
                  inv H
                | H : _ el (_ ++ _) |- _ =>
                  apply in_app_or in H;cbn in H
                | _ => eauto 5 using subterm ; eauto 5 using subterm,subterm_lam_inv,In_extend,lookup_el,subterm_app_l,subterm_app_r
                end).
  Qed.

  Lemma adress_size:
    (forall s a, closT (s,a) el T -> a <= length H)
    /\ (forall s a, (s,a) el V -> a <= length H)
    /\ (forall s a b, heapEntryC (s,a) b el H -> a <= length H /\ b <= length H).
  Proof.
    induction i in R,T,V,H|-*.
    {inv R. cbn. intuition. inv H0. eauto using subterm. }
    replace (S n) with (n + 1) in R by omega.
    apply pow_add with (R:=step) in R. destruct R as [[[T' V'] H'] [R1 R2]].
    specialize IHn with (1:=R1) as (IH__T&IH__V&IH__H).
    eapply rcomp_1 in R2.
    inv R2.
    all:cbn in *.
    all:(repeat split;repeat intro;
         repeat lazymatch goal with
                  
                | H : (_,_)=(_,_) |- _ => inv H 
                | H : heapEntryC _ _=heapEntryC _ _ |- _ => inv H 
                | H : closT _ = closT _ |- _ => inv H
                | H : _ \/ _ |- _=> inv H
                | H : lookup H _ _ = Some _ |- _=> eapply lookup_el in H as (?&?)
                | H : appT = closT _ |- _ => inv H 
                | H : put _ _ = (_, _) |- _ =>
                  inv H
                | H : _ el (_ ++ _) |- _ =>
                  apply in_app_or in H;cbn in H
                | H : heapEntryC (_, _) _ el _ |- _ =>
                  eapply IH__H in H as []
                (*| _ => once ((rewrite IH__H + rewrite IH__V + rewrite IH__T);[easy|])*)
                | _ => simpl_list;cbn; eauto 5 ;
                      try now (rewrite <- Nat.le_add_r; eauto 5)
                end).
  Qed.

  Lemma largestVarH_leq : largestVarH H <= largestVar s0.
    edestruct subterm_property as (_&_&H').
    apply largestVarH_bound. intros [] ? H''%(H' _ _).
    eapply subterm_lam_inv in H''.
    eapply subterm_largestVar. easy.
  Qed.

  Lemma largestVarC_V_leq : forall g, g el V -> largestVarC g <= largestVar s0.
    edestruct subterm_property as (_&H'&_).
    intros [] H''. apply H' in H''.  eapply subterm_lam_inv in H''. eapply subterm_largestVar. easy.
  Qed.
  
  (** *** Space *)
(*
  Lemma size_clos P a : ((P,a) el (T++V) -> sizeP P <= 2*size s0 /\ a <= length H)
                        /\ (forall beta, heapEntryC (P,a) beta el H -> sizeP P <= 2*size s0 /\ a <= length H /\ beta <= length H).
  Proof.
    unfold sizeP. 
    induction i in T,V,H,R,P,a|-*.
    -inv R. split.
     +intros [[= <- <-]|[]].
      eauto using sizeP_size,Nat.le_0_l.
     +intros ? [].
    -replace (S n) with (n + 1) in R by omega.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     split.
     +intros Hel.
      apply in_app_or in Hel.
      inv R2. 
      *apply jumpTarget_eq in H2.  cbn in H2;inv H2.
       destruct Hel as [[ [= <- <-]| ]|[[= <- <-] | ]]. 
       
       all:repeat (autorewrite with list in *;cbn in * ).
       1:specialize (proj1 (IHn _ a0) ltac:(eauto)).
       3:specialize (proj1 (IHn _ a0) ltac:(eauto)). 
       
       1,3:repeat (autorewrite with list in *;cbn in * ).
       1,2:omega.

       1:specialize (proj1 (IHn P a) ltac:(eauto)).
       2:specialize (proj1 (IHn P a) ltac:(eauto)). 

       all:omega. 

      *inv H2.
       destruct Hel as [[[= <- <-] | [[= <- <-]|]]|].  
       all:repeat ((try setoid_rewrite in_app_iff in IHn);cbn in IHn). 
       1:specialize (proj1(IHn Q _) ltac:(eauto)). 
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn _ a0) ltac:(eauto)). 
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn P a) ltac:(eauto)). 
       1:autorewrite with list in IHn. 
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn P a) ltac:(eauto)). 
       1:autorewrite with list in IHn. 
       1:repeat (autorewrite with list in *;cbn in * ).
       1:try now omega.
      *destruct Hel as [[[= <- <-]|]|[-> | ]].

       all:repeat ((try setoid_rewrite in_app_iff in IHn);cbn in IHn). 
       1:specialize (proj1(IHn _ a0) ltac:(eauto)). 
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn _ a) ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:apply lookup_el in H2 as (?&?). 
       1:specialize (proj2 (IHn _ a) _ ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn _ a) ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.
      * apply IHn. intuition.
     +intros ? Hel. inv R2.
      1,3,4:now apply IHn.
      inv H2.
      apply in_app_or in Hel.
      edestruct Hel as [|[[= -> ->]|[]]].
      1:specialize (proj2(IHn _ a) _ ltac:(eauto)).
      all:autorewrite with list;cbn.
      now omega.
      1:specialize (proj1(IHn _ a) ltac:(eauto)).
      1:specialize (proj1(IHn _ beta) ltac:(eauto)).
      omega.
  Qed.

  Lemma largestVar_bound : (forall q, q el T -> largestVarC q <= largestVar s0)
                           /\ (forall q, q el V -> largestVarC q <= largestVar s0)
                           /\ (forall q beta, heapEntryC q beta el H -> largestVarC q <= largestVar s0).
  Proof.
    induction i in T,V,H,R|-*.
    -inv R. repeat split.
     +intros ? [<-|[]]. cbn. 
      now rewrite largestVar_compile.
     +intros ? [].
     +intros ? ? [].
    -replace (S n) with (n + 1) in R by omega.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     destruct IHn as [IHn1 [IHn2 IHn3]].
     eapply rcomp_1 in R2.
     repeat split;intros q.
     +intros Hel.
      inv R2. 
      *apply jumpTarget_eq in H2.  cbn in H2;inv H2.
       cbn in IHn1.
       assert (max (largestVarP Q) (largestVarP P') <= largestVar s0).
       { unfold largestVarP. erewrite <- IHn1. 2:left;reflexivity. cbn. autorewrite with list. cbn.
         rewrite !maxl_app. cbn. Lia.lia. }
       destruct Hel as [<- | ].
       all:cbn in *.  all:try Lia.lia. all:intuition.
      *inv H2.
       cbn in *.
       destruct Hel as [<- | [<-|]].
       all:cbn.
       --erewrite <- IHn2 with (q:=(_,_)). cbn. reflexivity. eauto.
       --erewrite <- IHn1 . unfold largestVarP. 2:now left;eauto. cbn. Lia.lia.
       --eauto.
      *destruct Hel as [<-|]. cbn.
       --erewrite <- IHn1 . unfold largestVarP. 2:now left;eauto. cbn. Lia.lia.
       --eauto.
      *eauto.
     +intros Hel.
      inv R2. 
      *apply jumpTarget_eq in H2.  cbn in H2;inv H2.
       cbn in IHn1.
       assert (max (largestVarP Q) (largestVarP P') <= largestVar s0).
       { unfold largestVarP. erewrite <- IHn1. 2:left;reflexivity. cbn. autorewrite with list. cbn.
         rewrite !maxl_app. cbn. Lia.lia. }
       destruct Hel as [<- | ].
       all:cbn in *.  all:try Lia.lia. all:intuition.
      *inv H2.
       cbn in *. eauto. 
      *destruct Hel as [<-|].
       --apply lookup_el in H2 as (?&?). eauto.
       --eauto.
      *eauto.
     +intros ? Hel. inv R2.
      1,3,4:now eauto.
      inv H2.
      apply in_app_or in Hel.
      edestruct Hel as [|[[= -> ->]|[]]].
      --eauto.
      --eauto.
  Qed. *)
(*
  
  Inductive subterm (u:term) :term -> Prop :=
    subterm_here: subterm u u
  | subterm_lam s: subterm u s -> subterm u (lam s)
  | subterm_appL (s t:term): subterm u s -> subterm u (s t)
  | subterm_appR (s t:term): subterm u t -> subterm u (s t).

  Definition isSuffix {X} (P Q:list X) := exists pre, pre++P=Q.
  
  Definition isCA P : Prop := exists s', (s0=s' \/ subterm (lam s') s0) /\  isSuffix P (compile s').

  Instance isSuffix_PO X: PreOrder (@isSuffix X).
  Proof.
    split.
    -exists []. reflexivity.
    -intros ? ? ? (a&<-) (b&<-).
     exists (b++a). now autorewrite with list.
  Qed.

  Lemma compile_isCA s':
    (s0 = s' \/ subterm (lam s') s0) -> isCA (compile s').
  Proof.
    intros. exists s'. split. eauto. reflexivity.
  Qed.
  
  Lemma all_subterm :
    (forall q, q el T -> isCA (fst q))
    /\ (forall g, g el V -> exists s, fst g = compile s0 /\ subterm (lam s) s0)
    /\ (forall g b, heapEntryC g b el H ->  exists s, fst g = compile s0 /\ subterm (lam s) s0).
  Proof.
    induction i in T,V,H,R|-*.
    {inv R. repeat split. 2,3:easy.
     -intros ? [<-|[]]. cbn. eauto using compile_isCA. }
    replace (S n) with (n + 1) in R by omega.
    apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
    specialize (IHn _ _ _ R1).
    destruct IHn as [IHT [IHV IHH]].
    eapply rcomp_1 in R2.
    inv R2.
    -repeat eapply conj. 3:easy.
     all:intros ? [<-|];[|now eauto].
     +specialize IHT with (1:=or_introl eq_refl). cbn in IHT |-*.

      Lemma compile_start_lamT_subterm P0 P1 s :
        lamT :: P1 = compile s ++ P0
        -> exists s' rem, subterm (lam s') s
                   /\ compile s = compile (lam s')++rem
                   /\ P1 = compile s' ++ retT :: rem ++ P0.
      Proof.
        induction s as [n|s IHs t _ | s IHs] in P0,P1|-*.
        all:cbn. all:intros eq.
        -inv eq.
        -rewrite <- !app_assoc in eq.
         specialize IHs with (1:=eq) as (s'&eqm&eq1&eq2&->).
         rewrite eq2. cbn.
         eexists s',(eqm ++ compile t ++[appT]). cbn. repeat (try rewrite !app_assoc_reverse;cbn).
         repeat split. eauto using subterm.
        -exists s,[]. inv eq. autorewrite with list.
         repeat split. eauto using subterm.
      Qed.

        
      Lemma isCA_lamT P :
        isCA (lamT :: P)
        -> exists s' P', subterm (lam s') s0
                   /\ P = compile s' ++ retT :: P'.
      Proof.
        intros (s&sub&suf).
        specialize (compile_start_lamT_subterm) with (P0:=[]) as H'.
        setoid_rewrite app_nil_r in H'.
        specialize H' with (2:=)
        pose (rem:=@nil Tok).
        replace (pre ++ lamT :: P = compile s0) with (pre ++ [lamT] ++ P ++rem= compile s0++rem) in suf by now (subst rem;autorewrite with list).
        clearbody rem.
        induction s0 as [n | s0 IHs t0 IHt | s0 IHs] in rem,sub,suf,pre,P|-*.
        -rewrite !app_assoc in suf. eapply app_inv_tail in suf. exfalso. destruct pre as [|?[]];inv suf.
        -cbn in suf.
         specialize IHs with (P:=)
         autorewrite with list in suf. cbn in suf,IHs,IHt|-*.
         eapply IHs in suf.
        admit. -exfalso. cbn in *.
        
        -> jumpTarget 0 [] P = Some (Q, P')
        ->isCA P'
     all:firstorder.
    repeat split;intros q.
    +intros Hel.
     inv R2. 
     *apply jumpTarget_eq in H2.  cbn in H2;inv H2.
      cbn in IHn1.
      assert (max (largestVarP Q) (largestVarP P') <= largestVar s).
       { unfold largestVarP. erewrite <- IHn1. 2:left;reflexivity. cbn. autorewrite with list. cbn.
         rewrite !maxl_app. cbn. Lia.lia. }
       destruct Hel as [<- | ].
       all:cbn in *.  all:try Lia.lia. all:intuition.
      *inv H2.
       cbn in *.
       destruct Hel as [<- | [<-|]].
       all:cbn.
       --erewrite <- IHn2 with (q:=(_,_)). cbn. reflexivity. eauto.
       --erewrite <- IHn1 . unfold largestVarP. 2:now left;eauto. cbn. Lia.lia.
       --eauto.
      *destruct Hel as [<-|]. cbn.
       --erewrite <- IHn1 . unfold largestVarP. 2:now left;eauto. cbn. Lia.lia.
       --eauto.
      *eauto.
     +intros Hel.
      inv R2. 
      *apply jumpTarget_eq in H2.  cbn in H2;inv H2.
       cbn in IHn1.
       assert (max (largestVarP Q) (largestVarP P') <= largestVar s).
       { unfold largestVarP. erewrite <- IHn1. 2:left;reflexivity. cbn. autorewrite with list. cbn.
         rewrite !maxl_app. cbn. Lia.lia. }
       destruct Hel as [<- | ].
       all:cbn in *.  all:try Lia.lia. all:intuition.
      *inv H2.
       cbn in *. eauto. 
      *destruct Hel as [<-|].
       --apply lookup_el in H2 as (?&?). eauto.
       --eauto.
      *eauto.
     +intros ? Hel. inv R2.
      1,3,4:now eauto.
      inv H2.
      apply in_app_or in Hel.
      edestruct Hel as [|[[= -> ->]|[]]].
      --eauto.
      --eauto.
  Qed.

  Lemma Hcompile:
    (forall g b, heapEntryC g b el H -> exists s0, fst g = compile s0)
    /\ (forall g, g el V -> exists s0, fst g = compile s0)
    /\ (forall g, g el T -> exists P0 s0, fst g = compile s0).
  Proof.
    induction i in T,V,H,R|-*.
    {inv R. easy. }
    replace (S n) with (n + 1) in R by omega.
    apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
    specialize (IHn _ _ _ R1).
    eapply rcomp_1 in R2.
    inv R2.
    -split. repeat eapply conj.
    all:try now apply IHn.
    -
    -
    -
    -
    all:try cbn;firstorder.
    1,3,4:now omega.
    inv H2. autorewrite with list. cbn. omega.
*)    

  Lemma length_H : length H <= i.
  Proof.
    induction i in T,V,H,R|-*.
    -inv R. cbn;omega.
    -replace (S n) with (n + 1) in R by omega.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     inv R2.
     1,3,4:now omega.
     inv H2. autorewrite with list. cbn. omega.
  Qed.

  Lemma length_TV : length T + length V <= 2*i + 1.
  Proof.
    induction i in T,V,H,R|-*.
    -inv R. cbn. omega.
    -replace (S n) with (n + 1) in R by omega.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     inv R2.
     all:cbn in *. all:try omega.
  Qed.


  Lemma list_bound X size m (A:list X):
    (forall x, x el A -> size x <= m) -> sumn (map size A) <= length A * m.
  Proof.
    induction A;cbn;intros H'. omega.
    rewrite IHA. rewrite H'. omega. tauto. intuition.
  Qed.
(*
  Lemma correctSpace:
    sizeSt (T,V,H) <= 2*(i + 1) * (3*i+4*size s0).
  Proof.
    cbn. rewrite <- sumn_app,<-map_app. unfold sizeH.
    rewrite list_bound with (size:=sizeC) (m:=2*size s0 + i).
    rewrite list_bound with (size:=sizeHE) (m:=2*size s0 + 2*i).
    rewrite length_H. rewrite app_length,length_TV.
    lia.
    -intros [[]] H'. cbn - [mult sizeP]. edestruct size_clos as [H1 H2].
     apply H2 in H' as (->&->&->).
     rewrite length_H. omega.
    -intros [] H'. cbn - [mult sizeP]. edestruct size_clos as [H1 H2].
     apply H1 in H' as (->&->).
     rewrite length_H. omega.
  Qed.  *)

End Analysis.
