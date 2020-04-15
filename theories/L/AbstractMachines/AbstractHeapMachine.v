From Undecidability.L Require Import L AbstractMachines.Programs Complexity.ResourceMeasures.

Require Import Lia.

Import L_Notations.

  (** ** Abstract Heap Machine *)
Section Lin.

  Let HA:=nat.

  Notation clos := (Pro * HA)%type.

  Inductive heapEntry := heapEntryC (g:clos) (alpha:HA).

  (** *** Heaps *)
  
  Let Heap := list heapEntry.
  Implicit Type H : Heap.
  Definition put H e := (H++[e],|H|).
  Definition get H alpha:= nth_error H alpha.
  Definition extended H H' := forall alpha m, get H alpha = Some m -> get H' alpha = Some m.

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

  Fixpoint lookup H alpha x : option clos:=
    match get H alpha with
      Some (heapEntryC bound env') =>
      match x with
        0 => Some bound
      | S x' => lookup H env' x'
      end
    |  _ => None
    end.

 (** *** Reduction Rules *)

  Definition state := (list clos * list clos *Heap)%type.

  Hint Transparent state : core.

  Inductive step : state -> state -> Prop :=
    step_pushVal P P' Q a T V H:
      jumpTarget 0 [] P = Some (Q,P')
      ->step (((lamT::P),a)::T,V,H) ((P',a)::T,(Q,a)::V,H)
  | step_beta a b g P Q H H' c T V:
      put H (heapEntryC g b) = (H',c)
      -> step ((appT::P,a)::T,g::(Q,b)::V,H) ((Q,c) ::(P,a)::T,V,H')
  | step_load P a x g T V H:
      lookup H a x = Some g
      -> step ((varT x::P,a)::T,V,H) ((P,a)::T,g::V,H)
  | step_nil a T V H: step (([],a)::T,V,H) (T,V,H).

  Hint Constructors step : core.

  (** *** Unfolding *)
  
  Inductive unfolds H a: nat -> term -> term -> Prop :=
  | unfoldsUnbound k n :
      n < k ->
      unfolds H a k (var n) (var n)
  | unfoldsBound k b P s s' n:
      n >= k ->
      lookup H a (n-k) = Some (P,b) ->
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

  Inductive reprC : Heap -> clos -> term -> Prop :=
    reprCC H P s a s' :
      reprP P s ->
      unfolds H a 0 s s' ->
      reprC H (P,a) s'.
  
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
      all:try eassumption;try omega.
     +econstructor. omega.      
    -rename s into u.
     assert (H':lookup H a' (n-k) = Some (P,b)).
     {destruct n. omega. rewrite Nat.sub_succ_l. cbn. rewrite H1. now rewrite Nat.sub_succ in H2. omega. }
     rewrite bound_closed_k.
     2:{ eapply bound_ge with (k:=0). 2:omega. now eauto using unfolds_bound. }
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

  Lemma reprC_extend H H' g s:
    extended H H' ->
    reprC H g s ->
    reprC H' g s.
  Proof.
    inversion 2. subst. eauto using reprC, unfolds_extend.
  Qed.

  (** *** Time *)
  
  Lemma correctTime' s t k s0 P a T V H:
  timeBS k s t -> unfolds H a 0 s0 s ->
  exists g l H', reprC H' g t
            /\ pow step l ((compile s0++P,a)::T,V,H)
                  ((P,a)::T,g::V,H') /\ l = 4*k+1 /\ extended H H'.
  Proof.
    intros Ev R.
    induction Ev in s0,P,a,T,V,H,R |-*.
    -inversion R.
     +subst k s' s0. clear H0 R. rename P0 into Q,H3 into R.
      rewrite Nat.sub_0_r in H1.
      eexists (Q , b),1,H.
      repeat split.
      *eauto using reprC.
      *cbn [compile]. apply (rcomp_1 step).  now constructor. 
      *hnf. tauto.
     +subst k s' s0. clear R. rename H3 into R.
      eexists (compile s1 , a),1,H.
      repeat split.
      *eauto using reprC,reprP,unfolds.
      *cbn [compile Datatypes.app]; autorewrite with list;cbn [Datatypes.app].
       apply (rcomp_1 step). constructor. apply jumpTarget_correct.
      *hnf. tauto.
    -inv R. 
     {exfalso. inv H3. inv H4. } 
     rename t0 into t1. rename H5 into I__s, H6 into I__t.
     cbn [compile List.app]; autorewrite with list; cbn [List.app]. 
     specialize (IHEv1 _ (compile t1 ++ appT ::P) _ T V _ I__s)
       as ([P__temp a2]&k1&Heap1&rep1&R1&eq_k1&Ext1).
     inv rep1. inv H4. inv H6. rename H3 into I__s'.
     apply (unfolds_extend Ext1) in I__t.
     specialize (IHEv2 _ (appT ::P) _ T ((compile s2,a2)::V) _ I__t)
                 as (g__t&k2&Heap2&rep2&R2&eq2&Ext2).
     edestruct (put Heap2 (heapEntryC g__t a2)) as [Heap2' a2'] eqn:eq.
     assert (Ext2' := (put_extends eq)).
     apply ( reprC_extend Ext2') in rep2.
     apply ( unfolds_extend Ext2) in I__s'. apply ( unfolds_extend Ext2') in I__s'.

     specialize (unfolds_subst (get_current eq) rep2 I__s') as I__subst.
     edestruct (IHEv3 _ [] _ ((P,a)::T) V _ I__subst) as (g__u&k3&Heap3&rep3&R3&eq3&Ext3).
     eexists g__u,_,Heap3. 
     split;[ | split;[| split]].
     +eassumption.
     +apply pow_add. eexists. split.
      { exact R1. }
      apply pow_add. eexists. split.
      { exact R2. }
      apply pow_add. eexists. split.
      { apply (rcomp_1 step). constructor;eassumption. }
      autorewrite with list in R3.
      apply pow_add. eexists. split.
      {exact R3. }
      now apply (rcomp_1 step); constructor.
     +lia.
     +rewrite Ext1,Ext2,Ext2',Ext3. reflexivity.
  Qed.
  
  Definition init s :state := ([(compile s,0)],[],[]).

  
  Lemma correctTime s t k:
    timeBS k s t -> closed s ->
    exists g H, reprC H g t
           /\ pow step (4*k+2) (init s)
                  ([],[g],H).
  
  Proof.
    intros H1 H2.
    edestruct (correctTime' (s0:=s) (a:=0) (H:=[]) [] [] [] H1)
      as (g&l&H'&rep&R&eq&_).
    -apply bound_unfolds_id. eauto using closed_k_bound.
    -autorewrite with list in R.
      exists g,H'. split. assumption.
     replace (4 * k + 2) with ((4 * k + 1)+1) by omega.
     apply pow_add. eexists;split. subst l;eassumption.
     apply (rcomp_1 step). constructor. 
  Qed.

End Lin.

Notation clos := (Pro * nat)%type.


Lemma lookup_el H alpha x e: lookup H alpha x = Some e -> exists beta, heapEntryC e beta el H.
Proof.
  induction x in alpha, e|-*.
  all:cbn. all:unfold get. all:destruct nth_error as [[]|] eqn:eq.
  all:intros [= eq'].
  1:subst.
  all:eauto using nth_error_In.
Qed.

Section Analysis.

  Variable s : term.
 (* Hypothesis cs : closed s.*)
  Variable T V : list clos.
  Variable H: list heapEntry.
  Variable i : nat.

  Hypothesis R: pow step i (init s) (T,V,H).


  Lemma jumpTarget_eq c c0 c1 c2: jumpTarget 0 c0 c = Some (c1,c2) -> c1++[retT]++c2=c0++c.
  Proof.
    generalize 0 as k. 
    induction c as [|[]] in c1,c2,c0|-*;cbn. congruence.
    all:intros ? H'.
    4:destruct k;[inv H';congruence|].
    all:apply IHc in H'. 
    all:autorewrite with list in *.
    all:now cbn in *. 
  Qed.

  (** *** Space *)

  Lemma size_clos P a : ((P,a) el (T++V) -> sizeP P <= 2*size s /\ a <= length H)
                        /\ (forall beta, heapEntryC (P,a) beta el H -> sizeP P <= 2*size s /\ a <= length H /\ beta <= length H).
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

  Lemma length_TV : length T + length V <= 1+i.
  Proof.
    induction i in T,V,H,R|-*.
    -inv R. cbn;omega.
    -replace (S n) with (n + 1) in R by omega.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     inv R2.
     all:cbn in *. all:omega.
  Qed.

  Definition sizeC g :=
    match g with
      (P,a) => sizeP P + a 
    end.
  Definition sizeHE e :=
    match e with
      heapEntryC g b => sizeC g + b
    end.
  Definition sizeH H :=
    sumn (map sizeHE H).

  Definition sizeSt '(T,V,H) := sumn (map sizeC T) + sumn (map sizeC V) + sizeH H.

  Lemma list_bound X size m (A:list X):
    (forall x, x el A -> size x <= m) -> sumn (map size A) <= length A * m.
  Proof.
    induction A;cbn;intros H'. omega.
    rewrite IHA. rewrite H'. omega. tauto. intuition.
  Qed.

  Lemma correctSpace:
    sizeSt (T,V,H) <= (i + 1) * (3*i+4*size s).
  Proof.
    cbn. rewrite <- sumn_app,<-map_app. unfold sizeH.
    rewrite list_bound with (size:=sizeC) (m:=2*size s + i).
    rewrite list_bound with (size:=sizeHE) (m:=2*size s + 2*i).
    rewrite length_H. rewrite app_length,length_TV.
    lia.
    -intros [[]] H'. cbn - [mult sizeP]. edestruct size_clos as [H1 H2].
     apply H2 in H' as (->&->&->).
     rewrite length_H. omega.
    -intros [] H'. cbn - [mult sizeP]. edestruct size_clos as [H1 H2].
     apply H1 in H' as (->&->).
     rewrite length_H. omega.
  Qed.  

End Analysis.
