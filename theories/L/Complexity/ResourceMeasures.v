From Undecidability.L Require Import L.
Require Import RelationClasses.

(** * Resource Measures *)
(** ** Big-Step Time Measure*)

Inductive timeBS : nat -> term -> term -> Prop :=
  timeBSVal s : timeBS 0 (lam s) (lam s)
| timeBSBeta (s s' t t' u : term) i j k l: timeBS i s (lam s') -> timeBS j t (lam t') -> timeBS k (subst s' 0 (lam t')) u -> l = (i+j+1+k) -> timeBS l (s t) u.


Module Leftmost.

  (** ** Leftmost reduction *)

  Reserved Notation "s '≻lm' t" (at level 50).

  Inductive step_lm : term -> term -> Prop :=
  | step_lmApp  s t     : app (lam s) (lam t) ≻lm subst s 0 (lam t)
  | step_lmAppR s t  t' : t ≻lm t' -> app (lam s) t ≻lm app (lam s) t'
  | step_lmAppL s s' t  : s ≻lm s' -> app s t ≻lm app s' t
  where "s '≻lm' t" := (step_lm s t).
  Hint Constructors step_lm.

  Lemma step_lm_functional :
    functional step_lm.
  Proof.
    intros s t t' H1 H2.
    induction H1 in t',H2|-*;inv H2;try easy;try congruence. all:f_equal. all:apply IHstep_lm;eauto.
  Qed.
  

  Ltac inv_step_lm :=
    match goal with
    | H : step_lm (lam _) _ |- _ => inv H
    | H : step_lm (var _) _ |- _ => inv H
    | H : star step_lm (lam _) _ |- _ => inv H
    | H : star step_lm (var _) _ |- _ => inv H
    end.


  (** *** Small-Step_Lm Time Measure *)

  Instance pow_step_lm_congL k:
    Proper ((pow step_lm k) ==> eq ==> (pow step_lm k)) app.
  Proof.
    intros s t R u ? <-. revert s t R u.
    induction k;cbn in *;intros ? ? R ?. congruence. destruct R as [s' [R1 R2]].
    exists (s' u). firstorder.
  Defined.

  Instance pow_step_lm_congR k:
    Proper (eq ==>(pow step_lm k) ==> (pow step_lm k)) (fun s t => app (lam s) t).
  Proof.
    intros s ? <- t u R. revert s t u R.
    induction k;cbn in *;intros ? ? ? R. congruence. destruct R as [t' [R1 R2]].
    exists (lam s t'). firstorder.
  Defined.

  Instance step_lm_step: subrelation step_lm step.
  Proof.
    induction 1;eauto using step.
  Qed.

  (** *** Small-Step_Lm Space Measure *)

  Definition redWithMaxSizeL := redWithMaxSize size step_lm.

  Lemma redWithMaxSizeL_congL m m' s s' t:
    redWithMaxSizeL m s s' -> m' = (1 + m + size t) -> redWithMaxSizeL m' (s t) (s' t).
  Proof.
    intros R Heq.
    induction R as [s | s s'] in m',t,Heq |-* .
    -apply redWithMaxSizeR. cbn. omega. 
    -eapply redWithMaxSizeC. now eauto using step_lm. apply IHR. reflexivity.
     subst m m'. cbn. repeat eapply Nat.max_case_strong;omega.
  Qed.

  Lemma redWithMaxSizeL_congR m m' s t t':
    redWithMaxSizeL m t t' -> m' = (1 + m + size (lam s)) -> redWithMaxSizeL m' (lam s t) (lam s t').
  Proof.
    intros R Heq.
    induction R as [t | t t'] in m',s,Heq |-* .
    -apply redWithMaxSizeR. cbn in *. omega. 
    -eapply redWithMaxSizeC. now eauto using step_lm. apply IHR. reflexivity.
     subst m m'. cbn -[plus]. repeat eapply Nat.max_case_strong;omega.
  Defined.


  Lemma step_lm_evaluatesIn s s' t k: s ≻lm s' -> timeBS k s' t -> timeBS (S k) s t.
  Proof.
    intros H; induction H in t,k|-*; intros;  try inv H0; eauto 20 using timeBS.
    eapply IHstep_lm in H4. econstructor; eauto. omega. 
  Qed.

  Lemma timeBS_correct_lm s t k:
    (timeBS k s t <-> pow step_lm k s t /\ lambda t).
  Proof.
    split.
    -intros R.
     induction R.
     +unfold pow;cbn. eauto.
     +destruct IHR1 as [R1']. 
      destruct IHR2 as [R2'].
      destruct IHR3 as [R3'].
      split;[|assumption].
      subst l.
      replace (i+j+1+k) with (i+(j+(1+k))) by omega. 
      eapply pow_add.
      eexists;split.
      eapply pow_step_lm_congL;now eauto.
      eapply pow_add.
      eexists;split.
      eapply pow_step_lm_congR;now eauto.
      eapply pow_add.
      eexists;split.
      eapply (rcomp_1 step_lm). eauto.
      eauto. 
    -intros [R lt].
     induction k in s,t,R,lt,R|-*.
     +inv R. inv lt. constructor.
     +change (S k) with (1+k) in R. eapply pow_add in R as (?&R'&?).
      eapply (rcomp_1 step_lm) in R'. eapply step_lm_evaluatesIn;eauto 10.
  Qed.

  (** *** Big-Step_Lm Space Measure*)

  Inductive spaceBS : nat -> term -> term -> Prop :=
    spaceBSVal s : spaceBS (size (lam s)) (lam s) (lam s)
  | spaceBSBeta (s s' t t' u : term) m1 m2 m3 m:
      spaceBS m1 s (lam s') ->
      spaceBS m2 t (lam t') ->
      spaceBS m3 (subst s' 0 (lam t')) u ->
      m = max (m1 + 1 + size t)
              (max (size (lam s') + 1 + m2) m3) ->
      spaceBS m (s t) u.

  Lemma spaceBS_ge s t m: spaceBS m s t -> size s<= m /\ size t <= m.
  Proof.
    induction 1. omega.
    subst m. cbn -[plus]. all:(repeat apply Nat.max_case_strong;try omega).
  Qed.

  Lemma step_lm_evaluatesSpace s s' t m: s ≻lm s' -> spaceBS m s' t -> spaceBS (max (size s) m) s t.
  Proof.
    intros H; induction H in t,m|-*; intros H'.
    -inv H'.
     +destruct s;inv H1. destruct (Nat.eqb_spec n 0);inv H0.
      all:repeat econstructor.
      all:cbn -[plus].
      all:(repeat apply Nat.max_case_strong;try omega).
     +destruct s;inv H. now destruct (Nat.eqb_spec n 0);inv H0.
      econstructor. 1,2:econstructor. cbn.
      econstructor.
      1-4:now eauto.
      cbn -[plus]. 
      (repeat apply Nat.max_case_strong;intros;try omega).
    -inv H'. inv H2.
     specialize (spaceBS_ge H3) as [? ?].
     specialize (spaceBS_ge H3) as [? ?].
     apply IHstep_lm in H3.
     specialize (spaceBS_ge H5) as [? ?].
     specialize (spaceBS_ge H3) as [_ H''].
     econstructor;[now eauto using spaceBS..|]. 
     revert H''. cbn -[plus] in *. 
     (repeat apply Nat.max_case_strong;intros;try omega).
    -inv H'.
     specialize (spaceBS_ge H2) as [? ?].
     eapply IHstep_lm in H2.
     specialize (spaceBS_ge H2) as [_ H7].
     specialize (spaceBS_ge H3) as [? ?].

     econstructor.
     1-3:eassumption.
     revert H7.
     cbn -[plus] in *. 
     (repeat apply Nat.max_case_strong;intros;try omega).
  Qed.

  Lemma spaceBS_correct_lm s t m:
    spaceBS m s t <-> 
    redWithMaxSizeL m s t /\ lambda t.
  Proof.
    split.
    -intros R. induction R.
     +repeat econstructor.
     +destruct IHR1 as (R1'&?). 
      destruct IHR2 as (R2'&?).
      destruct IHR3 as (R3'&?).
      split;[|firstorder].
      subst m.
      eapply redWithMaxSize_trans with (t:=(lam s') t).
      { eapply redWithMaxSizeL_congL. eassumption. reflexivity. }
      
      eapply redWithMaxSize_trans with (t:=(lam s') (lam t')).
      { eapply redWithMaxSizeL_congR. eassumption. reflexivity. }
      econstructor. constructor. eassumption. reflexivity. reflexivity.
      specialize (spaceBS_ge R2) as [_ H3];cbn in H3.   
      cbn - [plus]. repeat eapply Nat.max_case_strong;omega.
    -intros (R&H).
     induction R as [t | s s' t m].
     +inv H;rename x into t. eauto using spaceBS.
     +inv H;rename m' into m. eapply step_lm_evaluatesSpace. eassumption. eauto.
  Qed.

  Lemma spaceBS_eval s t m:
    spaceBS m s t -> eval s t.
  Proof.
    intros (R&L) % spaceBS_correct_lm.
    split. 2:tauto.
    eapply redWithMaxSize_star in R.
    induction R. reflexivity. econstructor;eauto using step_lm_step.
  Qed.

End Leftmost.

Definition hasTime k s := exists t, evalIn k s t.
Definition hasSpace m s := maxP (fun m => exists s', s >* s' /\ m = size s' ) m.

Lemma hasSpace_iff m s :
  hasSpace m s <-> (forall s', s >* s' -> size s' <= m) /\ (exists s', s >* s' /\ size s' = m).
Proof.
  unfold hasSpace,maxP. firstorder.
Qed.

Lemma step_timeBS k s s' t: step s s' -> timeBS k s' t -> timeBS (S k) s t.
Proof.
  intros R E. induction R in k,E,t|-*.
  -eauto using timeBS.
  -inv E. eapply IHR in H2. econstructor. all:eauto;omega.
  -inv E. eapply IHR in H1. econstructor. all:eauto;omega.
Qed.

Lemma timeBS_evalIn s t k :
  timeBS k s t <-> evalIn k s t.
Proof.
  split.
  -induction 1 as [|? ? ? ? ? ? ? ? ? ? [IH1 ?] ? [IH2 ?] ? [IH3 ?]].
   +split. reflexivity. eauto.
   +unfold evalIn in *. split. 2:now eauto.
    subst l. rewrite <- !Nat.add_assoc.
    eapply pow_trans. now eapply pow_step_congL;eauto.
    eapply pow_trans. now eapply pow_step_congR;eauto.
    eapply pow_trans. eapply (rcomp_1 step). eauto.
    eauto. 
  -unfold evalIn.
   induction k in s |- *.
   +unfold pow;cbn. intros [-> H]. inv H. constructor.
   +intros [(?&?&?) L]. eapply step_timeBS. all:eauto.
Qed.

Lemma hasSpaceVal s : hasSpace (size (lam s)) (lam s).
Proof.
  econstructor.
  -repeat econstructor.
  -intros ? (?&R&?). inv R. all:easy.
Qed.

(** TODO: decompose this into lemmata? *)

Lemma hasSpaceBeta s s' m1 t t' m2 m3:
  hasSpace m1 s -> hasSpace m2 t ->
  s >* lam s' -> eval t t' ->
  hasSpace m3 (subst s' 0 t') ->
  hasSpace (max m3 (m1+m2+1)) (s t).
Proof.
  intros H1 H2 R1 R2 [(u0&R'3&LB3) UB3].
  split.
  -destruct H1 as [(s0&R'1&LB1) _]. destruct H2 as  [(t0&R'2&LB2) _].
   apply Nat.max_case_strong;intros ?.
   +exists u0. rewrite R1. rewrite R2. rewrite step_Lproc. 2:now apply R2. easy.
   +exists (s0 t0). split.
    *eapply star_step_app_proper. all:easy.
    *cbn. omega.
  -destruct H1 as [_ LB1]. destruct H2 as [_ LB2].
   intros m' (u1 & Ru & lequ1). remember (s t) as st eqn:eqst.
   eapply Nat.max_le_iff.  
   induction Ru as [? |? ? Ru Ru'] in s,t,lequ1, eqst, LB1, LB2,R1,R2 |-*;subst x.
   +right. rewrite lequ1.
    erewrite <- LB1, <- LB2. 2,3:eexists;split;[reflexivity|reflexivity].
    cbn;omega.
   +inv Ru'.
    *left. apply UB3. 
     replace s' with s0 in *.
     2:{ inv R1. all:easy. } 
     replace t' with (lam t0) in *.
     2:{ destruct R2 as [R2 H]. inv H. inv R2. all:easy. }
     eauto.
    *assert (R2'':eval t'0 t').
     {destruct R2 as [R2 H']. inv H'.
      split. 2:easy.
      eapply equiv_lambda. easy.
      rewrite <- H2, R2. reflexivity. }
     eapply IHRu.
     5,6:reflexivity.
     1,3-4:eassumption.
     intros ? (?&?&?). apply LB2. eexists. rewrite H2. eauto.
    *assert (R1'':s'0 >* (lam s')).
     {eapply equiv_lambda. easy.
      rewrite <- H2, R1. reflexivity. }
     eapply IHRu.
     5-6:reflexivity.
     2-4:eassumption.
     intros ? (?&?&?). apply LB1. eexists. rewrite H2. eauto.
Qed.

Lemma spaceBS_hasSpace m s t:
  Leftmost.spaceBS m s t -> exists m', hasSpace m' s /\ m <= m'.
Proof.
  induction 1 as [| s s' t t' u m1 m2 m3 m BS1 (m1'&IS1&leq1) BS2 (m2'&IS2&leq2) BS3 (m3'&IS3&leq3) ->].
  -do 2 eexists. apply hasSpaceVal. reflexivity.
  -eexists. split.
   eapply hasSpaceBeta. 1-2,5:eassumption.
   1,2:eapply Leftmost.spaceBS_eval;eauto.
   {
     eapply Leftmost.spaceBS_ge in BS1 as [].
     eapply Leftmost.spaceBS_ge in BS2 as [].
     eapply Leftmost.spaceBS_ge in BS3 as [].
     repeat eapply Nat.max_case_strong;omega.
   }
Qed.

Lemma hasSpace_step m s s':
  hasSpace m s -> s ≻ s' -> exists m', hasSpace m' s' /\ m' <= m.
Proof. 
  (* this needs bounded search for come up with m' *)
Abort.
    

   
