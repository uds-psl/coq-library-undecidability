From Undecidability.L Require Import L.
From Undecidability.LAM Require Import Prelims LM LM_code.

(** *Abstract Machine *)
Section Lin.

  Let HA:=nat.

  Inductive clos :=
    closC (P:Pro) (a:HA).
  Notation "P ! a" := (closC P a) (at level 40).

  Inductive heapEntry := null|heapEntryC (g:clos) (alpha:HA).

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

  Lemma get_next H H' m b: put H m = (H',b) -> extended H H'.
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

  (* stackStack and Heap *)
  Definition state := (list clos * list clos *Heap)%type.

  Hint Transparent state.

  Definition tailRecursion P a T : list clos :=
    match P with
      [] => T
    |  _ => (P!a)::T
    end.

  Inductive step : state -> state -> Prop :=
    step_pushVal P P' Q a T V H:
      jumpTarget 0 [] P = Some (Q,P')
      ->step ((lamT::P)!a::T,V,H) (tailRecursion P' a T,Q!a::V,H)
  | step_beta a b g P Q H H' c T V:
      put H (heapEntryC g b) = (H',c)
      -> step ((appT::P)!a::T,g::Q!b::V,H) (Q!c ::tailRecursion P a T,V,H')
  | step_load P a x g T V H:
      lookup H a x = Some g
      -> step ((varT x::P)!a::T,V,H) (tailRecursion P a T,g::V,H).

  Hint Constructors step.

  Inductive unheapedEnv H : HA -> list LM_code.clos  -> Prop :=
    unheapedEnvCons a P pCd b E' : get H a = Some (heapEntryC P b)
                                          -> unheapedClos H P pCd
                                          -> unheapedEnv H b E' -> unheapedEnv H a (pCd::E')
  | unheapedEnvNil a: get H a = Some null -> unheapedEnv H a []
  with unheapedClos H : clos -> LM_code.clos -> Prop :=
       | unheapedClosC a P E: unheapedEnv H a E
                                  -> unheapedClos H (P!a) (P/E).


  Hint Constructors unheapedEnv unheapedClos.
  Scheme unheapedEnv_mutual_ind := Induction for unheapedEnv Sort Prop
    with unheapedClos_mutual_ind := Induction for unheapedClos Sort Prop.
  Combined Scheme unheaped_mutual_ind from unheapedEnv_mutual_ind, unheapedClos_mutual_ind.

  Inductive represents : state -> LM_code.state -> Prop :=
  | representsC H T V T' V': Forall2 (unheapedClos H) T T' -> Forall2 (unheapedClos H) V V' -> represents (T,V,H) (T',V').

  Hint Constructors represents.

  Lemma unheaped_extend H H': extended H H' -> (forall a' E',unheapedEnv H a' E' -> unheapedEnv H' a' E')/\(forall p pCd,unheapedClos H p pCd -> unheapedClos H' p pCd).
  Proof.
    intros. apply unheaped_mutual_ind;intros.
    all:eauto 10 using get_current,get_next.
  Qed.

  Lemma unheapedEnv_extend H H' a' E' : extended H H' -> unheapedEnv H a' E' -> unheapedEnv H' a' E'.
  Proof.
    intros ext. eapply (unheaped_extend ext).
  Qed.

  Lemma unheapedClos_extend H H' p pCd: extended H H' ->unheapedClos H p pCd -> unheapedClos H' p pCd.
  Proof.
    intros ext. eapply (unheaped_extend ext).
  Qed.

  Lemma unheapedClos_tailRecursion H c alpha A T T': Forall2 (unheapedClos H) (c!alpha::T) (c/A::T') -> Forall2 (unheapedClos H) (tailRecursion c alpha T) (LM_code.tailRecursion c A T').
  Proof.
    destruct c as [|[]];cbn. 1,5:now inversion 1. all:tauto.
  Qed.

  Ltac invAll :=
    repeat
      match goal with
      | [H:represents (_::_,_) _ |- _] => inv H
      | [H:represents _ (_,_::_) |- _] => inv H
      | [H:unheapedClos _ _ _ |-_] => inv H
      | [H:Forall2 _ (_::_) _ |- _] => inv H
      | [H:Forall2 _ _ (_::_) |- _] => inv H
      | [H:Forall2 _ _ [] |- _] => inv H
      end.

  Lemma lookup_unheapedEnv H alpha E x p : unheapedEnv H alpha E -> lookup H alpha x = Some p -> exists q, nth_error E x = Some q /\ unheapedClos H p q.
  Proof.
    induction x in p,alpha,E|-*;cbn;intros uE eq.
    -inv uE;rewrite H0 in *. all:inv eq. eauto.
    -inv uE;rewrite H0 in *. now eauto. congruence.
  Qed.

  Lemma nth_error_unheapedEnv H alpha E x q : unheapedEnv H alpha E -> nth_error E x = Some q -> exists p, lookup H alpha x = Some p /\ unheapedClos H p q.
  Proof.
    induction x in q,alpha,E|-*;cbn;intros uE eq.
    -inv uE. 2:congruence. inv eq. rewrite H0.  eauto.
    -inv uE. 2:congruence. rewrite H0. eapply IHx. all:eauto.
  Qed.

  Lemma downSim': simulatedWith (LM_code.step) step (flip represents).
  Proof.
    intros ? ? ? S R. inv R; inv S; invAll;unfold flip.
    1:edestruct (put H (heapEntryC (P0 ! a) a0)) eqn:eq.
    3:edestruct nth_error_unheapedEnv as (?&?&?);[eassumption..|invAll].
    all:eexists;split;[|try now (econstructor;eauto 10)].
    all:repeat econstructor;eauto 10 using unheapedClos_tailRecursion,unheapedEnv_extend,unheapedClos_extend,unheapedClos_extend,Forall2_impl,get_next,get_current.
  Qed.

  Definition representsTerm H e s := exists e', unheapedClos H e e' /\ LM_code.representsValue e' s.
(*
  Lemma completeness s t c0 C V H C1 V1 alpha E Env:
    unheapedEnv H alpha E -> 
    Forall2 representsValue E Env
    -> Forall2 (unheapedClos H) C C1
    -> Forall2 (unheapedClos H) V V1
    -> bound (length E) s
    -> eval (psubst s 0 Env) t -> 
    exists p H', representsTerm H' p t /\ star step ((compile s++c0)!alpha::C,V,H) (tailRecursion c0 alpha C,p::V,H') /\ extended H H'.
  Proof.
    intros. 
    edestruct LM_code.completeness as (p&rep&R). 1-3:eassumption.
    eapply simulatedWithStar with (1:= downSim') in R as ([[T' V'] H']&rep'&R').
    revert R'. refine (_ : star step ((compile s ++ c0)!alpha::C,V,H) _ -> _ ). intros R'. 
    2:{cbv [flip]. econstructor. econstructor. constructor. eauto. all:eauto. }
    cbv [flip] in rep'.  invAll. 
    remember (psubst s 0 Env) as s' eqn:eq.
    induction Ev in s,c0,E,Env,C,V,repE,eq,dcl |- *.
    -destruct s;inv eq.
     +rewrite <- minus_n_O in H0. destruct _ eqn:eq;[|now inv H0]. subst t. 
      edestruct Forall2_nth2 as (p&?&?);eauto.
      exists p. cbn. eauto using R_star.
     +eexists;split. eauto. 
      eapply R_star. cbn.
      autorewrite with list.
      cbn. constructor. apply jumpTarget_correct.
    -destruct s; inv eq.
     +exfalso. destruct _ eqn:eq;inv H0. edestruct Forall2_nth2 as (p&?&?);eauto. inv H0.
     +cbn. autorewrite with list. cbn. 
      inv dcl. 
      edestruct IHEv1 as (p1&rep1&R1).
      1-3: try reflexivity;now eauto.
      inv rep1. 
      edestruct IHEv2 as (p2&rep2&R2).
      1-3: try reflexivity;now eauto.
      inv rep2.     
      edestruct IHEv3 with (c0:=@nil Tok)  as (p3&rep3&R3).
      3: now rewrite <-psubst_cons;eauto using representsValue_closedEnv.
      now eauto.
      now inv H4. 
      
      exists p3. split. now eauto. 
      inv rep3. 
      rewrite R1,tailRecursion_compile,R2. cbn.
      eapply starC. unfold tailRecursion. now eauto.
      autorewrite with list in R3. 
      exact R3.
  Qed.
*)
  Definition init s :state := ([compile s!0],[],[null]).

End Lin.
Notation "a ! alpha" := (closC a alpha) (at level 40).

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

  Lemma tailRecursion_incl c alpha T': tailRecursion c alpha T' <<= c!alpha::T'.
  Proof.
    destruct c as [|[]];cbn. all:eauto.
  Qed.

  Lemma tailRecursion_length c alpha T': | tailRecursion c alpha T'| <= 1+ length T'.
  Proof.
    destruct c as [|[]];cbn. all:eauto.
  Qed.

  Lemma size_clos P a : ((P!a) el (T++V) -> sizeP P <= 2*size s /\ a <= length H)
                        /\ (forall beta, heapEntryC (P!a) beta el H -> sizeP P <= 2*size s /\ a <= length H /\ beta <= length H).
  Proof.
    unfold sizeP. 
    induction i in T,V,H,R,P,a|-*.
    -inv R. split.
     +intros [[= <- <-]|[]].
      eauto using sizeP_size,Nat.le_0_l.
     +intros ? [H|[]]. inv H.
    -replace (S n) with (n + 1) in R by omega.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     split.
     +intros Hel.
      apply in_app_or in Hel.
      inv R2. 
      *apply jumpTarget_eq in H2.  cbn in H2;inv H2.
       destruct Hel as [H1|[[= <- <-] | ]]. 
       apply tailRecursion_incl in H1 as [[= <- <-]|].
       
       all:repeat (autorewrite with list in *;cbn in * ).
       1:specialize (proj1 (IHn _ a0) ltac:(eauto)).
       3:specialize (proj1 (IHn _ a0) ltac:(eauto)). 
       
       1,3:repeat (autorewrite with list in *;cbn in * ). 
       1,2:omega.

       1:specialize (proj1 (IHn P a) ltac:(eauto)).
       2:specialize (proj1 (IHn P a) ltac:(eauto)). 

       all:omega. 

      *inv H2.
       destruct Hel as [[[= <- <-] | ]|]. 
       2:apply tailRecursion_incl in H as [[= <- <-]|].
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
      *destruct Hel as [|[-> | ]].
       apply tailRecursion_incl in H0 as [[= <- <-]|].

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
     +intros ? Hel. inv R2.
      1,3:now apply IHn.
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

  Lemma length_H : length H <= 1+i.
  Proof.
    induction i in T,V,H,R|-*.
    -inv R. cbn;omega.
    -replace (S n) with (n + 1) in R by omega.
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     inv R2.
     1,3:now omega.
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
     all:cbn in *.  
     specialize (tailRecursion_length P' a T0). omega.
     1,2:specialize (tailRecursion_length P a T0).
     1,2:omega. 
  Qed.
  
(* Damit: länge eines zustandes beschränkt durch (i+i)*(3*(i+1)+2*|s|)*)
  

End Analysis.
