From Undecidability.L.Tactics Require Export LClos.
Require Import FunInd. 
Open Scope LClos.

(** *** Closure calculus interpreter *)

Definition CompBeta s t :=
  match s,t with
    |CompClos (lam ls) A,CompClos (lam lt) B => Some (CompClos ls (CompClos (lam lt) B::A))
    |_,_ => None
  end.

Definition CompAppCount j u v :=
  match u,v with
    (l,u),(k,v) => (j+(l+k),CompApp u v)
  end.

Fixpoint CompSeval n (u: nat * Comp) : nat * Comp:=
  match n with
      S n =>
      match u with
        | (l,CompApp s t) =>
          match CompBeta s t with
            | Some u => CompSeval n (S l,u)
            | None => CompSeval n (CompAppCount l (CompSeval n (0,s)) (CompSeval n (0,t)))
          end
        | (l,CompClos (app s t) A) => CompSeval n (l,(CompClos s A) (CompClos t A))
        | (l,CompClos (var x) A) => (l,nth x A (CompVar x))
        | u => u 
      end
    | _ => u
  end.

Lemma CompBeta_validComp s t u: validComp s -> validComp t -> CompBeta s t = Some u -> validComp u.
Proof with repeat (auto || congruence || subst || simpl in * || intuition).
  intros vs vt eq. inv vs; inv vt... destruct s0... destruct s,s0... inv eq. repeat constructor... inv H1...
Qed.
(*
Lemma CompBeta_lamComp s t u: CompBeta s t = Some u -> (lamComp s /\ lamComp t).
Proof with repeat (auto || congruence || subst || simpl in.
  unfold CompBeta. intros equ. destruct s,t... destruct s... destruct s... destruct s,s0...
Qed.

Lemma CompBeta_lamComp2 s t: CompBeta s t = None -> (~lamComp s \/ ~lamComp t).
Proof with repeat inv_validComp;try (intros ?;repeat inv_validComp).
  unfold CompBeta. intros equ. destruct s,t;try now left... right... destruct s. left... left... destruct s0... right... right... congruence.
Qed.
*)
Lemma CompSeval_validComp s k n: validComp s -> validComp (snd (CompSeval n (k,s))).
Proof with repeat (apply validCompApp ||apply validCompClos || eauto || congruence || subst || simpl in * || intuition). 
  revert s k. induction n; intros s k vs... inv vs...
  case_eq (CompBeta s0 t);intros...
  -apply CompBeta_validComp in H1...
  -assert (IHn1 := IHn s0 0 H). assert (IHn2 := IHn t 0 H0).
   unfold snd in *. do 2 destruct ((CompSeval n (_,_)))...
  -destruct s0...
Qed.

Hint Resolve CompSeval_validComp.

Lemma CompBeta_sound s t u: CompBeta s t = Some u -> s t >[(1)] u.
Proof with repeat (auto || congruence || subst || simpl in * || intuition).
  intros eq. destruct s,t... destruct s... destruct s... destruct s... destruct s0... inv eq. repeat constructor...
Qed.

Functional Scheme CompSeval_ind := Induction for CompSeval Sort Prop.

Lemma CompSeval_sound' n s l : let (k,t) := CompSeval n (l,s) in k >= l /\ s >[(k-l)] t.
Proof with (repeat inv_validComp;repeat (constructor || intuition|| subst ; eauto using star || rewrite Nat.sub_diag||cbn in *)).
  pose (p:= (l,s)).
  change (let (k, t) := CompSeval n p in k >= fst p /\ (snd p) >[(k-(fst p))] t).
  generalize p. clear l s p. intros p. 
  functional induction (CompSeval n p); intros;cbn...
  -apply CompBeta_sound in e2. destruct (CompSeval _ _);split... eapply CPow_trans;try  eassumption. omega.
  -repeat destruct (CompSeval _ _)... eapply CPow_trans...
  -repeat destruct (CompSeval _ _)... eapply CPow_trans...
Qed.

Lemma CompSeval_sound (n k:nat) s t : CompSeval n (0,s) = (k,t) -> s >[(k)] t.
Proof.
  specialize (CompSeval_sound' n s 0). destruct _;intros.
  inv H0. rewrite <- minus_n_O in H. tauto.
Qed.

                                        (*
Lemma CompSeval_lam' n s: lamComp s -> CompSeval n s = s.
Proof.
  intros ls. now destruct ls, n. 
Qed.

Lemma CompSeval_mono' n s: CompSeval n s >[]* CompSeval (S n) s.
Proof with repeat inv_validComp;repeat (constructor || simpl in * || subst ; eauto using star).
  revert s. induction n;intros.
  -destruct s;simpl.
   +reflexivity.
   +case_eq (CompBeta s1 s2);intros... apply CompBeta_sound in H...
   +destruct s,A;try destruct n...
  -remember (S n) as m. rewrite Heqm at 1. simpl. destruct s. reflexivity. case_eq (CompBeta s1 s2);intros;rewrite !IHn... destruct s,A;try destruct n0...
Qed.

Lemma CompSeval_mono n m s : n <= m -> CompSeval n s >[]* CompSeval m s.
Proof.
  intros R. revert s;induction R;intros.
  -reflexivity.
  -now rewrite IHR, CompSeval_mono'.
Qed.


Lemma CompSeval_complete s t: validComp s -> lamComp t -> s >[]* t -> exists n, CompSeval n s=t.
Proof with repeat (subst || intuition || eauto).
  revert t. induction s;intros t vc lt R.
  -inv R. exists 0. trivial. inv H.
  -assert (R':=R). apply CStep_Lam' in R' as [s1' [s2' [[R1 l1] [R2 l2]]]]... inv vc.
   specialize (IHs1 _ H1 l1 R1). destruct IHs1 as [n1 eq1].
   specialize (IHs2 _ H2 l2 R2). destruct IHs2 as [n2 eq2].
   pose (n:=max n1 n2). exists (S n). simpl. admit.
  -destruct s;simpl in R.
   *inv R. exists 0. trivial. inv H. eexists 1. simpl. SearchAbout inv vc.
    earchAbout lamComp. rewrite lamComp_star with (t:=CompSeval m' 0). SearchAbout lamComp. apply CompSeval_lam' in H7 with (n:=). rewrite CompSeval_mono with (n:=m1). inv H1. simpl. apply validComp_step... admit. auto 30. H5.  R' with (ARS.pow CStep n s' t). fold pow in R'. inv vc. inv R. 
  apply pow_revert t;induction s;intros t vc lt R.
  -inv vc. inv lt. inv R. simpl. 
  intros [cs [? ?]] t R. subst. simpl in R. inv R.
Qed.



Lemma CompSeval_complete s t: validComp s -> lamComp t -> s >[]* t -> exists n, CompSeval n s=t.
Proof with try subst;intuition;eauto.
  intros vc lt R. apply star_pow in R. destruct R as [n R]. revert s t vc lt R. apply complete_induction with (x:=n). clear n;intros. destruct x.
  -inv R. exists 0. trivial.
  -destruct R as [s' [R R']]. inv vc.
  +apply CStep_Lam in R'... decompose [and ex] R'. apply H in H1 as [m1 ?]... apply H in H5 as [m2 ?]... pose (m:=max m1 m2). exists (S m). simpl. rewrite lamComp_star with (t:=CompSeval m' 0). SearchAbout lamComp. apply CompSeval_lam' in H7 with (n:=). rewrite CompSeval_mono with (n:=m1). inv H1. simpl. apply validComp_step... admit. auto 30. H5.  R' with (ARS.pow CStep n s' t). fold pow in R'. inv vc. inv R. 
  apply pow_revert t;induction s;intros t vc lt R.
  -inv vc. inv lt. inv R. simpl. 
  intros [cs [? ?]] t R. subst. simpl in R. inv R.
Qed.













Lemma CompSeval_mono1 s t n: (~ lamComp t) -> t = CompSeval n s -> (exists n', n' >= n /\ ARS.pow CStep n' s t).
Proof with auto.
  revert s t. induction n. simpl;intros.
  -subst. exists 0;simpl. intuition.
  -intros. simpl in H0. destruct s. case_eq (CompBeta s1 s2);intros;rewrite H1 in H0.
   +apply IHn in H0 as [n' [ge R]]... exists (S n'). split. omega. exists c. split... apply CompBeta_correct in H1...
   +apply CompBeta_lamComp2 in H1 as [H1|H1].  exists (s1 s2). simpl. 

Lemma CompSeval_correct2'  s n: ~lamComp s -> exists k, CompSeval  s >[]> CompSeval (S n') s.
Proof.
  revert n'. induction s;intros n' neq. simpl. case_eq (CompBeta s1 s2);intros. apply CompBeta_correct in H. inv H. congruence. rewrite !IHn...

Lemma CompSeval_correct2 s t : lamComp t -> s >[]* t -> exists n, CompSeval n s = t.
Proof with auto.
  intros lt R. apply star_pow in R. destruct R as [n R]. revert s t lt R. induction n;intros.
  -inv R. exists 0...
  -destruct R as [u [R R']]. apply IHn in R' as [n' R']... exists (S n'). rewrite <- R'. simpl. inv R. subst. inv R. destruct s. destruct Rinv R.
  


(*
Lemma CompSeval_mono1 s t n:  validComp s -> s >[]* t -> CompSeval n s >[]*CompSeval n t.
Proof with repeat (inv_validComp || apply validCompApp || auto || eauto 2 using validComp_step || eauto using star,rStar'_trans_l,rStar'_trans_r || auto ||subst || intuition).
  revert s t. induction n;intros s t vs R.
  -simpl. now rewrite R.  
  -induction R. reflexivity.  assert (validComp y)... rewrite <- H1. clear H1 R z. simpl. inv vs;inv H0.
   assert ( A:=CompSeval_validComp n H1); inv A;rewrite H0.
   assert ( B:=CompSeval_validComp n H3); inv B;rewrite H7.
   
   rewrite IHn with (t:=s0)... rewrite IHn at 2. destruct ()inv vs;inv H0... inv H1;inv H3;try apply IHn... apply IHn in H'...  inv vs; inv H2;simpl in *.  inv H3;inv H5. apply IHn... destruct z1... try apply IHn... destruct t; try apply IHn... destruct s0; try apply IHn... apply CStep_star_subrelation in H0. apply IHn in H0... rewrite H0. destruct n;simpl... destruct s;try rewrite IHn... destruct t;try rewrite IHn... destruct s0;try rewrite IHn... repeat constructor;simpl... inv H6... inv_CompStep. inv H0... destruct s0;try rewrite IHn... destruct t;try rewrite IHn... destruct s;try rewrite IHn... intuition. simpl in *. inv H0. apply IHn... apply IHn... SearchAbout star CStep. rewrite IHn. apply stepAppL. apply IHn... simpl. destruct s,t. destruct s1,t1. apply IHn... apply IHn... auto. destruct vs1. repeat (constructor|| apply CompSeval_validComp);auto. apply Hint Resolve validComp_step.auto 30.
    destruct s. destruct s1. destruct t. 
  *)
(*
Lemma CompSeval_mono s t n m:  validComp s -> n<=m -> s >[]* t -> CompSeval n s >[]*CompSeval m t.
Proof with intuition;eauto.
  revert m s. induction n.
  -intros. simpl. rewrite H1. apply CompSeval_correct. eapply validComp_star;eauto. 
  -intros m. induction m; intros. omega.
   decide (n=m).
   +subst. simpl. inv H. destruct s. destruct s1.
    *clear IHm. specialize (IHn m). rewrite IHn.
   +subst. admit. rewrite IHm... omega. 
   simpl. destruct s. destruct s1. 
   
    vc lt. [t' A] eq m gt. clear t. revert m A s vs t' eq gt. induction n.
  -intros m. induction m;intros.
   +auto.
   +simpl. apply IHm. simpl. destruct s. destruct s1. simpl in *. erewrite <-!IHm. apply IHm in eq. simpl. assert (n=0) by omega. now subst.
  -simpl. destruct s. destruct s1. decide (m=n).
   +subst. auto. apply IHm in eq.
Qed.
*)

   Lemma CompSeval_correct2 s t: validComp s -> lamComp t -> s >[]* t -> exists n, CompSeval n s=t.
Proof with try subst;intuition;eauto.
  intros vc lt R. apply star_pow in R. destruct R as [n R]. revert s t vc lt R. apply complete_induction with (x:=n). clear n;intros. destruct x.
  -inv R. exists 0. trivial.
  -destruct R as [s' [R R']]. inv R; inv vc.
  +apply CStep_Lam in R'... decompose [and ex] R'. apply H in H1 as [m1 ?]... apply H in H5 as [m2 ?]... pose (m:=max m1 m2). apply CompSeval_lam with (n:=m) in H7. exists (S (max m1 m2)). simpl. inv H1. simpl. apply validComp_step... admit. auto 30. H5.  R' with (ARS.pow CStep n s' t). fold pow in R'. inv vc. inv R. 
  apply pow_revert t;induction s;intros t vc lt R.
  -inv vc. inv lt. inv R. simpl. 
  intros [cs [? ?]] t R. subst. simpl in R. inv R.
Qed.
*)
