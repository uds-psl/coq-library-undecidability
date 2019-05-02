From Undecidability.L Require Import L.
From Undecidability.LAM Require Import Prelims LM_lin LM.

(** ** Direct correctness proof  *)


Inductive reprP : Pro -> term -> Prop :=
  reprPC s : reprP (compile s) (lam s).

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

  Lemma tailRecursion_compile s P a T:
    tailRecursion (compile s ++ P) a T = ((compile s ++ P)!a)::T.
  Proof.
    induction s in P,T|-*.
    all:cbn.
    1,3:easy.
    rewrite <- app_assoc. rewrite IHs1. now autorewrite with list.
  Qed.

(** *** Unfolding *)

Inductive unfolds H a: nat -> term -> term -> Prop :=
| unfoldsUnbound k n :
    n < k ->
    unfolds H a k (var n) (var n)
| unfoldsBound k b P s s' n:
    n >= k ->
    lookup H a (n-k) = Some (P!b) ->
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
  -inv H2. inv H3. constructor. inv IHunfolds. eapply bound_ge. eauto. omega.
  -now constructor.
  -now constructor. 
Qed.


Inductive reprC : list heapEntry -> clos -> term -> Prop :=
  reprCC H P s a s' :
    reprP P s ->
    unfolds H a 0 s s' ->
    reprC H (P!a) s'.

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
    decide _. 
    econstructor. all:eauto.
    econstructor. all:eauto.    
   +decide _. econstructor; eauto. omega.
    econstructor. omega.
  -rename s into u.
   assert (H':lookup H a' (n-k) = Some (P!b)).
   {destruct n. omega. rewrite Nat.sub_succ_l. cbn. rewrite H1. now rewrite Nat.sub_succ in H2. omega. }
   rewrite bound_closed_k.
   2:{ eapply bound_ge with (k:=0). 2:omega. now eauto using unfolds_bound. }
   econstructor. all:try eassumption;omega.
  -econstructor. all:eauto.
  -econstructor. all:eauto.
   Unshelve. all: repeat econstructor.
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

Lemma reprC_extend H H' g s:
  extended H H' ->
  reprC H g s ->
  reprC H' g s.
Proof.
  inversion 2. subst. eauto using reprC, unfolds_extend.
Qed.

(** *** BS correctness *)

Lemma completeness' s t s0 P a T V H:
  eval s t -> unfolds H a 0 s0 s ->
  exists g H', reprC H' g t
            /\ star step (((compile s0++P)!a)::T,V,H)
                  (tailRecursion P a T,g::V,H') /\ extended H H'.
Proof.
  intros Ev R.
  induction Ev in s0,P,a,T,V,H,R |-*.
  -inversion R.
(*    +subst k s s0. clear H0 R. rename P0 into Q,H3 into R. *)
(*     rewrite Nat.sub_0_r in H1. *)
(*     eexists (Q ! b),H. *)
(*     repeat split. *)
(*     *eauto using reprC. *)
(*     *cbn [compile]. eapply R_star. now econstructor.  *)
(*     *hnf. tauto. *)
(*    +subst k s' s0. clear R. rename H3 into R. *)
(*     eexists (compile s1 ! a),H. *)
(*     repeat split. *)
(*     *eauto using reprC,reprP,unfolds. *)
(*     *cbn [compile Datatypes.app]; autorewrite with list;cbn [Datatypes.app]. *)
(*      apply R_star. constructor. apply jumpTarget_correct. *)
(*     *hnf. tauto. *)
(*   -inv R.  *)
(*    {exfalso. inv H2. inv H3. }  *)
(*    rename t0 into t1. rename H4 into I__s, H5 into I__t. *)
(*    cbn [compile List.app]; autorewrite with list; cbn [List.app].  *)
(*    specialize (IHEv1 _ (compile t1 ++ appT ::P) _ T V _ I__s) *)
(*      as ([P__temp a2]&Heap1&rep1&R1&Ext1). *)
(*    inv rep1. inv H4. inv H6. rename H3 into I__s'. *)
(*    apply (unfolds_extend Ext1) in I__t. *)
(*    specialize (IHEv2 _ (appT ::P) _ T ((compile s2!a2)::V) _ I__t) *)
(*      as (g__t&Heap2&rep2&R2&Ext2). *)
(*    edestruct (put Heap2 (heapEntryC g__t a2)) as [Heap2' a2'] eqn:eq. *)
(*    assert (Ext2' := (put_extends eq)). *)
(*    apply ( reprC_extend Ext2') in rep2. *)
(*    apply ( unfolds_extend Ext2) in I__s'. apply ( unfolds_extend Ext2') in I__s'. *)

(*    specialize (unfolds_subst (get_current eq) rep2 I__s') as I__subst. *)
(*    edestruct (IHEv3 _ [] _ (tailRecursion P a T) V _ I__subst) as (g__u&Heap3&rep3&R3&Ext3). *)
(*    eexists g__u,Heap3.  *)
(*    split;[ | split]. *)
(*    +eassumption. *)
(*    +rewrite R1,tailRecursion_compile,R2. cbn. *)
(*     eapply starC. *)
(*     {apply step_beta. eassumption. } *)
(*     autorewrite with list in R3. *)
(*     exact R3. *)
(*    +rewrite Ext1,Ext2,Ext2',Ext3. reflexivity. *)
(* Qed. *)
Admitted.

Definition init s :state := ([(compile s!0)],[],[]).

Lemma completeness s t:
  eval s t -> closed s ->
  exists g H, reprC H g t
         /\ star step (init s)
               ([],[g],H).

Proof.
  intros H1 H2.
  edestruct (completeness' (s0:=s) (a:=0) (H:=[]) [] [] [] H1)
    as (g&H'&rep&R&_).
  -apply bound_unfolds_id. eauto using closed_k_bound.
  -autorewrite with list in R.
   exists g,H'. split. assumption.
   exact R.
Qed.

(** *** BS soundness *)

Lemma soundness' s0 s P a T V H k sigma:
  evaluatesIn step k (((compile s0++P)!a)::T,V,H) sigma ->
  unfolds H a 0 s0 s ->
  exists k1 k2 g H' t, k = k1 + k2
                  /\ pow step k1 (((compile s0++P)!a)::T,V,H) (tailRecursion P a T,g::V,H')
                  /\ evaluatesIn step k2 (tailRecursion P a T,g::V,H') sigma
                  /\ eval s t
                  /\ extended H H'
                  /\ reprC H' g t.
Proof.
  revert s s0 P a T V H.
  induction k as [k IH] using lt_wf_ind .
  intros s s0 P a T V H [R Ter] Unf.
  induction s0 as [|s01 IHs01 s02 IHs02 | s0] in IH,k,s,Unf,T,R,P,V,H|-*.
  -inv Unf. omega.
   assert (exists k', k = 1 + k') as (k'&->).
   {destruct k. 2:eauto. exfalso.
    inv R. eapply Ter. econstructor. rewrite Nat.sub_0_r in *. eassumption. }
   apply pow_add in R as (?&R1&R2).
   apply rcomp_1 in R1. inv R1.
   rewrite Nat.sub_0_r in *.
   inv H3. inv H5.
   repeat esplit.
   +cbn. constructor. eassumption.
   +congruence.
   +eauto.
   + reflexivity.
   +reflexivity.
   + eauto using unfolds.
  -cbn in R. inv Unf.
   rewrite <- !app_assoc in R.
   pose (R':=R).
   eapply IHs01 in R' as (k11&k12&g1&H'1&t1&eq1&R11&[R1 _]&Ev1&Ext1&Rg1). 2-4:eassumption.
   rewrite tailRecursion_compile in R1.
   inv Rg1. inv H1. inv H2.
   pose (R':=R1).
   eapply IHs02 in R' as (k21&k22&g2&H'2&t2&eq2&R21&[R2 _]&Ev2&Ext2&Rg2).
   3-4:now eauto using unfolds_extend.
   2:{ intros. eapply IH. omega. all:eauto. }
   inv Rg2. inv H1. inv H2.
   cbn in R2.
   assert (exists k22', k22 = 1 + k22') as (k22'&->).
   {destruct k22. 2:eauto. exfalso.
    inv R2. eapply Ter. econstructor. reflexivity. }
   pose (R':=R2).
   apply pow_add in R' as (?&R2'&R3).
   apply rcomp_1 in R2'. inv R2'.
   specialize (put_extends H14) as Ext3.
   edestruct IH with (P:=@nil Tok) as (k31&k32&g3&H'3&t3&eq3&R31&[R3' _]&Ev3&Ext4&Rg3).
   2:now autorewrite with list;split;[exact R3|].
   now omega.
   {
    eapply unfolds_subst.
    -eauto using get_current.
    -eapply reprC_extend. 2:econstructor;eauto using reprP,unfolds. eauto.
    -eapply unfolds_extend. 2:eassumption. now rewrite Ext2,Ext3.
   }
   cbn in R3'.
   inv Rg3. inv H1.
   eexists (k11+(k21+(1+k31))),k32,_,_,_.
   repeat eexists.
   +omega.
   +cbn [compile]. autorewrite with list.
    rewrite app_nil_r in R31. cbn [tailRecursion]in R31.
    repeat (eapply pow_add with (R:=step);eexists;split).
    *eassumption.
    *rewrite tailRecursion_compile. eassumption.
    *cbn. eapply rcomp_1 with (R:=step). constructor. eassumption.
    *eassumption.
   +eassumption.
   +eassumption.
(*    +econstructor. all:eauto using eval, unfolds. *)
(*    +now rewrite Ext1,Ext2,Ext3. *)
(*    +eassumption. *)
(*   -inv Unf.  *)
(*    assert (exists k', k = 1 + k') as (k'&->). *)
(*    {destruct k. 2:eauto. exfalso. *)
(*     inv R. eapply Ter. cbn. econstructor. autorewrite with list. eapply jumpTarget_correct. } *)
(*    apply pow_add in R as (?&R1&R2). *)
(*    apply rcomp_1 in R1. inv R1. *)
(*    autorewrite with list in H8. cbn in H8. rewrite jumpTarget_correct in H8. inv H8. *)
(*    eexists 1,k',_,_,_. *)
(*    repeat esplit. *)
(*    +cbn. constructor. autorewrite with list. apply jumpTarget_correct. *)
(*    +congruence. *)
(*    +eauto. *)
(*    +constructor. *)
(*    +reflexivity. *)
(*    +eauto using unfolds. *)
(* Qed. *)
Admitted.
    
Lemma soundness s sigma:
  closed s -> 
  evaluates step (init s) sigma ->
  exists g H t, sigma = ([],[g],H) /\ eval s t /\ reprC H g t.
Proof.
  intros cs [R Ter].
  eapply star_pow in R as [k R].
  edestruct soundness' with (P:=@nil Tok) as (k1&k2&g&H&t&eq&R1&[R2 _]&Ev&_&Rgt).
  -split. rewrite app_nil_r. all:eassumption.
  -apply bound_unfolds_id. eapply closed_dcl. eassumption.
  -cbn in R2.
    assert (k2 = 0) as ->.
   {destruct k2. eauto. exfalso.
    destruct R2 as (?&R'&?). inv R'. }
   inv R2.
   repeat eexists. all:eauto.
Admitted.

(** ** Reduction *)

Definition reduces X Y (p : X -> Prop) (q : Y -> Prop) := exists f : X -> Y, forall x, p x <-> q (f x).
Notation "p ⪯ q" := (reduces p q) (at level 50).

Definition eva s := exists t, eval s t.

Definition evaLin sigma := exists tau, evaluates step sigma tau.


Lemma red_halt_L_to_LM_Lin s:
  closed s -> eva s <-> evaLin (init s).
Proof.
  intros ?.
  unfold eva, evaLin.
  split.
  -intros (t&R). eapply completeness in R as (g&Hp&_&R). 2:easy.
   eexists. split. eassumption.
   intros ? H'. inv H'.
  -intros (?&E).
   eapply soundness in E as (?&?&?&?&?&?). all:eauto.
Qed.

