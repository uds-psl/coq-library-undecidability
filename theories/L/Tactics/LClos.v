From Undecidability.Shared.Libs.PSL Require Import Base.
From Undecidability.L Require Export Util.L_facts.

(* **** Closure calculus *)

Inductive Comp : Type :=
| CompVar (x:nat)
| CompApp (s : Comp) (t : Comp) : Comp
| CompClos (s : term) (A : list Comp) : Comp.                      

Coercion CompApp : Comp >-> Funclass.

Inductive lamComp : Comp -> Prop := lambdaComp s A: lamComp (CompClos (lam s) A).

Inductive validComp : Comp -> Prop :=
| validCompApp s t : validComp s -> validComp t -> validComp (s t)
| validCompClos (s : term) (A : list Comp) :
     (forall a, a el A -> validComp a) -> (forall a, a el A -> lamComp a) -> bound (length A) s -> validComp (CompClos s A).

#[export] Hint Constructors Comp lamComp validComp : core.

Definition validEnv A := forall a, a el A -> validComp a (*/\ lamComp a)*).

Definition validEnv' A := forall a, a el A -> closed a.

#[export] Hint Unfold validEnv validEnv' : core.

Lemma validEnv_cons a A : validEnv (a::A) <-> ((validComp a) /\ validEnv A).
Proof.
  unfold validEnv. simpl. split. auto. intros [? ?] a' [eq|el']; subst;auto.
Qed.

Lemma validEnv'_cons a A : validEnv' (a::A) <-> (closed a /\ validEnv' A).
Proof.
  unfold validEnv'. simpl. intuition. now subst.
Qed.

Ltac inv_validComp :=
  match goal with
    | H : validComp (CompApp _ _) |- _ => inv H
    | H : validComp (CompClos _ _)   |- _ => inv H
  end.
  
Definition Comp_ind_deep'
           (P : Comp -> Prop)
           (Pl : list Comp -> Prop)
           (IHVar : forall x : nat, P (CompVar x))
           (IHApp : forall s : Comp, P s -> forall t : Comp, P t -> P (s t))
           (IHClos : forall (s : term) (A : list Comp),
                       Pl A -> P (CompClos s A))
           (IHNil : Pl nil)
           (IHCons : forall (a:Comp) (A : list Comp),
                       P a -> Pl A -> Pl (a::A))
           (x:Comp) : P x :=
  (fix f c : P c:=
     match c with
       | CompVar x => IHVar x
       | CompApp s t => IHApp s (f s) t (f t)
       | CompClos s A => IHClos s A 
         ((fix g A : Pl A := 
            match A with
                [] => IHNil
              | a::A => IHCons a A (f a) (g A)
            end) A)
     end) x
.

Definition Comp_ind_deep
           (P : Comp -> Prop)
           (IHVar : forall x : nat, P (CompVar x))
           (IHApp : forall s : Comp, P s -> forall t : Comp, P t -> P (s t))
           (IHClos : forall (s : term) (A : list Comp),
                       (forall a, a el A -> P a) -> P (CompClos s A)) : forall x, P x.
Proof.
  apply Comp_ind_deep' with (Pl:=fun A => (forall a, a el A -> P a));auto.
  intros. inv H1;auto. 
Qed.

(*
Lemma subst_comm s x1 u1 x2 u2 : closed u1 -> closed u2 -> x1 <> x2 -> subst (subst s x1 u1) x2 u2 = subst (subst s x2 u2) x1 u1.
Proof with try (congruence||auto).
  intros cl1 cl2 neq. revert x1 x2 neq;induction s;simpl;intros.
  -decide (n=x1); decide (n=x2); try rewrite cl1;try rewrite cl2;subst;simpl...
   +decide (x1=x1)...
   +decide (x2=x2)...
   +decide (n=x2);decide (n=x1)...
  -rewrite IHs1,IHs2...
  -rewrite IHs...
Qed.
*) (*
Lemma subst_twice s x u1 u2 : closed u1 -> subst (subst s x u1) x u2 = subst s x u1.
Proof with try (congruence||auto).
  intros cl. revert x;induction s;simpl;intros.
  -decide (n=x);subst. now rewrite cl. simpl. decide (n=x);subst;congruence. 
  -rewrite IHs1,IHs2...
  -rewrite IHs...
Qed.*)
(*
Lemma subst_free a s k u y: closed a -> subst s k u = s -> subst (subst s y a) k u = subst s y a.
Proof.
  intros ca eq. revert y k u eq. induction s;simpl;intros.
  -decide (n=y). now rewrite ca. apply eq.
  -simpl in eq. inversion eq. rewrite H0, H1, IHs1, IHs2;auto.
  -f_equal. simpl in eq. inversion eq. rewrite !H0. now rewrite IHs.
Qed.*)
(*
Lemma bound_ge k s m: bound k s -> m >= k -> bound m s.
Proof.
  intros. decide (m=k);subst.
  -auto.
  -eapply bound_gt;eauto. lia.
Qed.
*)
(*
Lemma bound_subst' x s a y:  bound x s -> closed a -> bound x (subst s y a).
Proof.
  intros dcl cl. revert y. induction dcl;simpl;intros.
  -decide (n=y);subst.
   +eapply bound_ge. now apply closed_dcl. lia.
   +now constructor.
  -now constructor.
  -now constructor.
Qed.
*)

(*
Fixpoint substList' (s:term) (x:nat) (A: list term): term := 
  match A with
    | nil => s
    | a::A => substList' (subst s x a) (S x) A
  end.*)

Fixpoint substList (s:term) (x:nat) (A: list term): term := 
  match s with
    | var n => if Dec (x>n) then var n else nth (n-x) A (var n)
    | app s t => app (substList s x A) (substList t x A)
    | lam s => lam (substList s (S x) A)
  end.
  

Fixpoint deClos (s:Comp) : term := 
  match s with
    | CompVar x => var x
    | CompApp s t => app (deClos s) (deClos t)
    | CompClos s A => substList s 0 (map deClos A)
  end.

(* Reduction *)

Reserved Notation "s '>[(' l ')]' t" (at level 50, format "s  '>[(' l ')]'  t").

Declare Scope LClos.

Inductive CPow : nat -> Comp -> Comp -> Prop :=
| CPowRefl (s:Comp) : s >[(0)] s                                                      
| CPowTrans (s t u:Comp) i j : s >[(i)] t -> t >[(j)] u -> s >[(i+j)] u
| CPowAppL (s s' t :Comp) l: s >[(l)] s' -> (s t) >[(l)] (s' t)                                  
| CPowAppR (s t t':Comp) l: t >[(l)] t' -> (s t) >[(l)] (s t')
| CPowApp  (s t:term) (A:list Comp) :
    CompClos (app s t) A >[(0)] (CompClos s A) (CompClos t A)
| CPowVar (x:nat) (A:list Comp):
    CompClos (var x) A >[(0)] nth x A (CompVar x)
| CPowVal (s t:term) (A B:list Comp):
    lambda t -> (CompClos (lam s) A) (CompClos t B) >[(1)] (CompClos s ((CompClos t B)::A))
where "s  '>[(' l ')]'  t" := (CPow l s t)  : LClos.

Open Scope LClos.

Ltac inv_CompStep :=
  match goal with
    | H : (CompApp _ _) >(_) CompClos _ _ |- _ => inv H
    | H : (CompClos _ _) >(_) CompApp _ _ |- _ => inv H
  end.

#[export] Hint Constructors CPow : core.

Lemma CPow_congL n s s' t :
  s >[(n)] s' ->  s t >[(n)] s' t.
Proof.
  induction 1;eauto.
Qed.

Lemma CPow_congR n (s t t' : Comp) :
  t >[(n)] t' ->  s t >[(n)] s t'.
Proof.
  induction 1;eauto.
Qed.

Lemma CPow_trans s t u i j k : s >[(i)] t -> t >[(j)] u -> i + j = k -> s >[(k)] u.
Proof.
  intros. subst. eauto.
Qed.


#[global]
Instance CPow'_App_properR n:
  Proper (eq ==> (CPow n) ==> (CPow n)) CompApp.
Proof.
  intros ? ? -> ? ?  ?. now eapply CPow_congR. 
Qed.
(*
Definition CStar s t:= exists k , CPow k s t .

Notation "s '>[]*' t" := (CStar s t) (at level 50)  : L.los.

Instance rStar'_PreOrder : PreOrder CStar.
Proof.
  constructor; hnf.
  -now eexists.
  -eapply star_trans. 
Qed.

Lemma rStar'_trans_l s s' t :
  s >[]* s' ->  s t >[]* s' t.
Proof.
  induction 1; eauto using star.
Qed.

Lemma rStar'_trans_r (s t t' : Comp):
  t >[]* t' -> s t >[]* s t'.
Proof.
  induction 1; eauto using star.
Qed.

Instance rStar'_App_proper :
  Proper ((star CStep) ==> (star CStep) ==> (star CStep)) CompApp.
Proof.
  cbv. intros s s' A t t' B. etransitivity.
  apply rStar'_trans_l, A. apply rStar'_trans_r, B.
Qed.

Instance CStep_star_subrelation : subrelation CStep (star CStep).
Proof.
  intros s t st. eauto using star.
Qed.

*)


(* Properties of step-indexed version *)
(*
Notation "x '>[]^' n y" := (ARS.pow CStep n x y) (at level 50) : L.cope.

Lemma CStep_Lam  n: forall (s t u:Comp), lamComp u -> (ARS.pow CStep n (s t) u) ->
                                       exists m1 m2 (s' t':Comp),(m1 < n /\ ARS.pow CStep m1 s s' /\ lamComp s')
                                                                 /\ (m2 < n /\ ARS.pow CStep m2 t t' /\ lamComp t').
Proof with repeat intuition;try now reflexivity.
  induction n;intros ? ? ? lu R.
  -inv R. inv lu.
  -destruct R as [u' [R R']]. inv R.
   +apply IHn in R'... decompose [ex and] R'. exists (S x), x0, x1, x2... change (S x) with (1+x). apply pow_add;simpl. exists s';intuition. eexists;simpl...
   +apply IHn in R'... decompose [ex and] R'. exists x, (S x0), x1, x2... change (S x0) with (1+x0). apply pow_add;simpl. exists t';intuition. eexists;simpl...
   +inv H2. eexists 0,0,_,_...
Qed.

Lemma CStep_Lam' (s t u:Comp) : lamComp u -> (s t) >[]* u ->
                         exists (s' t':Comp),( s >[]* s' /\ lamComp s')
                                             /\ (t >[]* t' /\ lamComp t').
Proof with repeat intuition;try now reflexivity.
  intros lu R. apply star_pow in R. destruct R as [n R]. revert s t u lu R. induction n;intros.
  -inv R. inv lu.
  -destruct R as [u' [R R']]. inv R.
   +apply IHn in R'... decompose [ex and] R'. exists x, x0... eauto using star. 
   +apply IHn in R'... decompose [ex and] R'. exists x, x0... eauto using star.
   +inv H2. eexists _,_...
Qed.



*)
Lemma substList_bound x s A: bound x s -> substList s x A = s.
Proof.
  revert x;induction s;intros;simpl.
  -inv H. decide (x>n);tauto.
  -inv H. now rewrite IHs1,IHs2.
  -inv H. rewrite IHs;auto. 
Qed.

Lemma substList_closed s A x: closed s -> substList s x A = s.
Proof.
  intros. apply substList_bound. destruct x. now apply closed_dcl. eapply bound_gt;[rewrite <- closed_dcl|];auto. lia.
Qed.

Lemma substList_var' y x A: y >= x -> substList (var y) x A = nth (y-x) A (var y).
Proof.
  intros ge. simpl. decide (x>y). lia. auto. 
Qed.

Lemma substList_var y A: substList (var y) 0 A = nth y A (var y).
Proof.
  rewrite substList_var'. f_equal. lia. lia.
Qed.

Lemma substList_is_bound y A s: validEnv' A -> bound (y+|A|) (s) -> bound y (substList s y A).
Proof.
  intros vA. revert y. induction s;intros y dA.
  -apply closed_k_bound. intros k u ge. simpl. decide (y>n). 
   +simpl. destruct (Nat.eqb_spec n k). lia. auto.
   +inv dA. assert (n-y<|A|) by lia. now rewrite (vA _ (nth_In A #n H)).
  -inv dA. simpl. constructor;auto.
  -simpl. constructor. apply IHs. now inv dA.
Qed.

Lemma substList_closed' A s: validEnv' A -> bound (|A|) (s) -> closed (substList s 0 A).
Proof.
  intros. rewrite closed_dcl. apply substList_is_bound;auto.
Qed.



Lemma deClos_valComp a: validComp a -> closed (deClos a).
Proof.
  intros va. induction va;simpl.
  -now apply app_closed.
  -apply substList_closed'. intros a ain. rewrite in_map_iff in ain. destruct ain as [a' [eq a'in]];subst. now apply H0. now rewrite map_length.
Qed.

Lemma deClos_validEnv A : validEnv A -> validEnv' (map deClos A).
Proof.
  intros vA. induction A;simpl.
  -unfold validEnv'. simpl. tauto.
  -rewrite validEnv'_cons.  apply validEnv_cons in vA as [ca cA]. split;auto. apply deClos_valComp; auto.
Qed.

#[export] Hint Resolve deClos_validEnv : core.

Lemma subst_substList x s t A: validEnv' A -> subst (substList s (S x) A) x t = substList s x (t::A).
Proof.
  revert x;induction s;simpl;intros x cl.
  -decide (S x > n);simpl. decide (x>n); destruct (Nat.eqb_spec n x);try lia;try tauto. subst. now rewrite minus_diag. decide (x>n). lia. destruct (n-x) eqn: eq. lia. assert (n2=n-S x) by lia. subst n2. destruct (nth_in_or_default (n-S x) A #n).
   + apply cl in i. now rewrite i.
   +rewrite e. simpl. destruct (Nat.eqb_spec n x). lia. auto. 
  -now rewrite IHs1,IHs2.
  -now rewrite IHs.
Qed.

Lemma validComp_step s t l: validComp s -> s >[(l)] t -> validComp t.
Proof with repeat (subst || firstorder).
  intros vs R. induction R;repeat inv_validComp...
  -inv H3. constructor...
  -inv H3. apply H1. apply nth_In. lia.
  -inv H8. constructor;auto;intros a [?|?];subst;auto.
Qed.

#[export] Hint Resolve validComp_step : core.
(*
Lemma deClos_correct''' s t : validComp s -> s >(0) t -> deClos s = deClos t.
Proof with repeat (cbn in * || eauto || congruence || lia || subst).
  intros cs R. remember 0 as n eqn:eq in R. revert eq. induction R;intros ?;repeat inv_validComp...
  -destruct i... rewrite IHR1,IHR2...
  -destruct IHR...
  -rewrite IHR...
  -simpl. rewrite <- minus_n_O. rewrite <-map_nth with (f:=deClos)...
Qed.

Lemma deClos_correct'' s t : validComp s -> s >(1) t -> deClos s = deClos t \/ deClos s ≻ deClos t.
Proof with repeat (cbn in * || eauto || congruence || lia || subst).
  intros cs R. remember 1 as n eqn:eq in R. revert eq. induction R;intros ?;repeat inv_validComp...
  -destruct i...
   +destruct IHR2... apply deClos_correct''' in R1... left... aply deClos_correct''' in R1... right...
    right... split;eauto. destruct IHR. auto.  left... right...
  -destruct IHR. auto.  left... right...
  -left...
  -left. simpl. rewrite <- minus_n_O. rewrite <-map_nth with (f:=deClos)...
  -right. inv H. simpl. rewrite <-subst_substList...
Qed.*)

Lemma deClos_correct l s t : validComp s -> s >[(l)] t -> deClos s >(l) deClos t.
Proof with repeat (cbn in * || eauto 10 using star || congruence || lia || subst).
  intros cs R.
  induction R...
  -eapply pow_trans;eauto.
  -inv cs;apply pow_step_congL...
  -inv cs;apply pow_step_congR...
  -rewrite <- minus_n_O. rewrite <-map_nth with (f:=deClos)...
  -inv H. inv cs. inv H1. eexists;split... rewrite <- subst_substList... 
Qed.

(*

(* relation that tries to capture that two closures 'reduce' to one another *)

Reserved Notation "s '=[]>' t" (at level 70).

Inductive reduceC : Comp -> Comp -> Prop :=
  | redC s t: deClos s >* deClos t -> s =[]> t
where "s '=[]>' t" := (reduceC s t).

#[export] Hint Constructors reduceC.

Lemma reduceC_if s t : s =[]> t -> deClos s >* deClos t.
Proof.
  now inversion 1.
Qed.


(* ** Properties of the extended reduction relation *)

Instance reduceC_PreOrder : PreOrder reduceC.
Proof.
  constructor;repeat intros;constructor.
  -reflexivity.
  -inv H. inv H0. now rewrite H1.
Qed.

Instance reduceC_App_proper :
  Proper (reduceC ==> reduceC ==> reduceC) CompApp.
Proof.
  cbv. intros s s' A t t' B. constructor. simpl. apply star_step_app_proper.
  -now inv A.
  -now inv B.
Qed.

Lemma CStep_reduceC l s t: validComp s -> s >(l) t -> s =[]> t.
Proof.
 intros. constructor. eapply deClos_correct;eauto.  
Qed.


(* relation that tries to capture that two closures 'are the same' *)

Reserved Notation "s '=[]=' t" (at level 70).

Inductive equivC : Comp -> Comp -> Prop :=
  | eqC s t: deClos s == deClos t -> s =[]= t
where "s '=[]=' t" := (equivC s t).

#[export] Hint Constructors equivC.

Lemma equivC_if s t : s =[]= t -> deClos s == deClos t.
Proof.
  now inversion 1.
Qed.


(* ** Properties of the equivalence relation *)

Instance equivC_Equivalence : Equivalence equivC.
Proof.
  constructor;repeat intros;constructor.
  -reflexivity.
  -inv H. now rewrite H0.
  -inv H0. inv H. now rewrite H0. 
Qed.

Instance equivC_App_proper :
  Proper (equivC ==> equivC ==> equivC) CompApp.
Proof.
  cbv. intros s s' A t t' B. constructor. simpl. apply equiv_app_proper.
  -now inv A.
  -now inv B.
Qed.

Lemma CStep_equivC s t: validComp s -> s >[]> t -> s =[]= t.
  intros vs R. induction R;repeat inv_validComp.
  -now rewrite IHR.
  -now rewrite IHR.
  -constructor. reflexivity.
  -constructor. simpl. rewrite <- minus_n_O. rewrite <-map_nth with (f:= deClos). reflexivity.
  -constructor. rewrite deClos_correct'. reflexivity. auto. auto. 
Qed.


Lemma starC_equivC s t :
  validComp s -> s >[]* t -> s =[]= t.
Proof.
  intros vs R. induction R.
  -reflexivity.
  -rewrite <-IHR.
   +eauto using CStep_equivC.
   +eauto using validComp_step.
Qed.

*)

Lemma substList_nil s x: substList s x [] = s.
Proof.
  revert x. induction s;intros;simpl.
  -decide (x>n). reflexivity. now destruct(n-x).
  -congruence.
  -congruence.
Qed.
(*
Lemma equivC_deClos s : s =[]> CompClos (deClos s) [].
Proof.
  constructor. simpl. induction s;simpl.
  -now destruct x.
  -rewrite IHs1 at 1. rewrite IHs2 at 1. reflexivity.
  -now rewrite substList_nil.
Qed.

 *)
(*
Goal uniform_confluent CStep.
Proof with try (congruence||(now (subst;tauto))||(now (right;eauto))||(now (right;eauto;eexists;eauto))).
  intros s. induction s;intros.
  -inv H.
  -inv H;inv H0...
   +destruct (IHs1 _ _ H4 H3) as [?|[? [? ?]]]...
   +destruct (IHs2 _ _ H4 H3) as [?|[? [? ?]]]...
   +inv H4; now inv H3.
   +inv H3; now inv H4.
  -inv H; inv H0...
Qed.*)
(*
Lemma lamComp_noStep l s t : lamComp s -> ~ s>(S l)t.
Proof.
  intros H R. remember (S l). revert Heqn. revert H. induction R;intros;try congruence.
  destruct i. inv H. inv R.lia. .
Qed.
*)
Lemma validComp_closed s: closed s -> validComp (CompClos s []).
Proof.
  intros cs. constructor;simpl;try tauto. now apply closed_dcl.
Qed.
(*
Lemma lamComp_star s t : lamComp s -> s >[]* t -> s = t.
Proof.
  intros H R. induction R. auto. now apply lamComp_noStep in H0.
Qed.

Lemma validComp_star s t: validComp s -> s >[]* t -> validComp t.
Proof.
  intros vs R. induction R; eauto using validComp_step.
Qed.

*)
(*
Lemma deClos_lam p s: (λ s) = deClos p -> exists t, lamComp t /\ deClos t = (lam s) /\ p >[]* t.
Proof.
  revert s. apply Comp_ind_deep with (x:=p);clear p;simpl.
  -congruence.
  -congruence.
  -intros p A IH s eq. destruct p; simpl in eq.
   +rewrite <- minus_n_O in eq. change (var n) with (deClos (CompVar n)) in eq. rewrite map_nth in eq. apply IH in eq as [t [? [? R]]]. exists t;repeat split;auto. now rewrite CStepVar. destruct (nth_in_or_default n A (CompVar n)).
    *auto.
    *rewrite e in eq. simpl in eq. congruence.
   +inv eq.
   +exists (CompClos (lam p) A). simpl.  repeat split;auto. reflexivity.
Qed.


Fixpoint normComp' s A:=
  match s with
    | app s t => (normComp' s A) (normComp' t A)
    | var x => CompClos (var x) A (*nth x A (CompVar x)*)
    | lam s => CompClos (lam s) A
  end.

Fixpoint normComp s :=
  match s with
    | CompApp s t => (normComp s) (normComp t)
    | CompClos s A => normComp' s A
    | s => s
  end.

Lemma normComp'_deClos s A: deClos (CompClos s A) = deClos (normComp' s A).
Proof.
  induction s;simpl.
  -rewrite <- minus_n_O. reflexivity.
  -simpl in *. congruence.
  -simpl in *. congruence.
Qed.


Lemma normComp_deClos s: deClos s = deClos (normComp s).
Proof.
  induction s;simpl.
  -auto.
  -congruence.
  -rewrite <- normComp'_deClos. reflexivity.
Qed.

Lemma normComp'_star s A: CompClos s A >[]* normComp' s A.
Proof.
  induction s;simpl;eauto using star.
  -rewrite CStepApp. now rewrite IHs1,IHs2.
Qed.

Lemma normComp_star s: s >[]* normComp s.
Proof.
  induction s;simpl.
  -reflexivity.
  -now rewrite <- IHs1,<-IHs2.
  -apply normComp'_star.
Qed.

Lemma normComp'_idem s A:normComp (normComp' s A)=normComp' s A.
Proof.
  induction s;simpl;  congruence. 
Qed.


Lemma normComp_idem s: normComp (normComp s)=normComp s.
Proof.
  induction s;simpl.
  -reflexivity.
  -congruence.
  -apply normComp'_idem.
Qed.


Lemma normComp'_valid s A: validComp (CompClos s A) -> validComp (normComp' s A).
Proof.
  intros vA. induction s;simpl.
  -auto.
  -inv vA. inv H3. auto. 
  -auto.
Qed.


Lemma normComp_valid s: validComp s -> validComp (normComp s).
Proof.
  intros vs. induction s;simpl.
  -auto.
  -inv vs. auto.
  -apply normComp'_valid. auto.
Qed.


Lemma CompStep_correct2' s t : normComp s = s -> validComp s -> deClos s ≻ t -> exists t', t = deClos t' /\ s >[]* t'.
Proof.
  intros nc vs. revert t. induction vs as [s1 s2|]; intros t R.
  -simpl in R. inv R;simpl in nc.
   +destruct (deClos_lam H0) as [t'[lt' [eq R]]]. 
    destruct (deClos_lam H1) as [u [lu [equ Ru]]].
    inv lt'. 
    exists (CompClos s0 (u::A)). simpl;split.
    *rewrite equ. rewrite <-subst_substList. simpl in eq. congruence. apply deClos_validEnv. apply validComp_star in R;auto. inv R. auto.
    *rewrite R, Ru. inv lu. rewrite <- CStepVal. reflexivity. auto.
   +apply IHvs2 in H2 as [u [? R]]. exists (s1 u). split; simpl. congruence. now rewrite R. congruence.  
   +apply IHvs1 in H2 as [u [? R]]. exists (u s2). split; simpl. congruence. now rewrite R. congruence.
  -destruct s;simpl in nc.
   +simpl in R. rewrite <- minus_n_O in R. change (var n) with (deClos (CompVar n)) in R. rewrite map_nth in R. apply H0 in R. destruct R as [t' [? ?]].
    *eexists. split. eauto. now rewrite CStepVar.
    *apply nth_In. now inv H2.
    *destruct (nth_in_or_default n A (CompVar n)). apply H1 in i. inv i. now simpl.  rewrite e. reflexivity.
   +inv nc.
   +simpl in R. inv R.
Qed.


Lemma CompStep_correct2 s t : validComp s -> deClos s ≻ t -> exists t', t = deClos t' /\ s >[]* t'.
Proof.
  intros vs R. rewrite normComp_deClos in R. destruct (CompStep_correct2' (normComp_idem s) (normComp_valid vs) R) as [t' [eq R']]. exists t'. split.  auto. now rewrite normComp_star.
Qed.

 
Close Scope L.los.*)
