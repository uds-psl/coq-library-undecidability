From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Export LClos_Eval.
From Undecidability.L.Tactics Require Import mixedTactics.
Require Import FunInd.

(** *** Reflexted closure calculus *)
(** This moduel provides definitions of an symbolic simplifier for reflected L-terms used in Lbeta *)

Open Scope LClos.

Inductive rTerm : Type :=
| rVar (x : nat) : rTerm
| rApp (s : rTerm) (t : rTerm) : rTerm
| rLam (s : rTerm)
| rConst (x : nat) : rTerm
| rRho (s : rTerm).

Coercion rApp : rTerm >-> Funclass.

Definition denoteTerm (phi : nat -> term) :rTerm->term :=
  fix denoteTerm s :=
    match s with
    | rVar n => var n
    | rApp s t=> app (denoteTerm s) (denoteTerm t)
    | rLam s => lam (denoteTerm s)
    | rConst n => phi n
    | rRho s => rho (denoteTerm s)
    end.

Definition Proc phi := forall (n:nat) , proc (phi n).

Definition rClosed phi s:= Proc phi /\ closed (denoteTerm phi s).

Definition rPow phi n s t :=
  denoteTerm phi s >(n) denoteTerm phi t.

Lemma rReduceIntro phi l s t : Proc phi -> rClosed phi s -> rClosed phi t -> denoteTerm phi s >(l) denoteTerm phi t -> rPow phi l s t.
  unfold rPow;tauto.
Qed.

Inductive rComp : Type :=
| rCompVar (x:nat)
| rCompApp (s : rComp) (t : rComp) : rComp
| rCompClos (s : rTerm) (A : list rComp) : rComp.

Coercion rCompApp : rComp >-> Funclass.


Definition denoteComp (phi : nat -> term) :rComp -> Comp:=
  fix denoteComp s :=
    match s with
    | rCompVar x => CompVar x
    | rCompApp s t => (denoteComp s) (denoteComp t)
    | rCompClos s A => CompClos (denoteTerm phi s) (map denoteComp A)
    end.

Fixpoint rSubstList (s:rTerm) (x:nat) (A: list rTerm): rTerm :=
  match s with
  | rVar n => if Dec ( n < x )then rVar n else nth (n-x) A (rVar n)
  | rApp s t => (rSubstList s x A) (rSubstList t x A)
  | rLam s => rLam (rSubstList s (S x) A)
  | rRho s => rRho (rSubstList s (S x) A)
  | rConst x => rConst x
  end.

Fixpoint rDeClos (s:rComp) : rTerm :=
  match s with
  | rCompVar x => rVar x
  | rCompApp s t => (rDeClos s) (rDeClos t)
  | rCompClos s A => rSubstList s 0 (map rDeClos A)
  end.


Definition rComp_ind_deep'
           (P : rComp -> Prop)
           (Pl : list rComp -> Prop)
           (IHVar : forall x : nat, P (rCompVar x))
           (IHApp : forall s : rComp, P s -> forall t : rComp, P t -> P (s t))
           (IHClos : forall (s : rTerm) (A : list rComp),
               Pl A -> P (rCompClos s A))
           (IHNil : Pl nil)
           (IHCons : forall (a:rComp) (A : list rComp),
               P a -> Pl A -> Pl (a::A))
           (x:rComp) : P x :=
  (fix f c : P c:=
     match c with
     | rCompVar x => IHVar x
     | rCompApp s t => IHApp s (f s) t (f t)
     | rCompClos s A => IHClos s A
                              ((fix g A : Pl A :=
                                  match A with
                                    [] => IHNil
                                  | a::A => IHCons a A (f a) (g A)
                                  end) A)
     end) x
.

Definition rComp_ind_deep
           (P : rComp -> Prop)
           (IHVar : forall x : nat, P (rCompVar x))
           (IHApp : forall s : rComp, P s -> forall t : rComp, P t -> P (s t))
           (IHClos : forall (s : rTerm) (A : list rComp),
               (forall a, a el A -> P a) -> P (rCompClos s A)) : forall x, P x.
Proof.
  apply rComp_ind_deep' with (Pl:=fun A => (forall a, a el A -> P a));auto.
  -intros. inv H1;auto.
Qed.

Definition rValidComp phi s := Proc phi /\validComp (denoteComp phi s).

Lemma rSubstList_correct phi s x A: Proc phi -> denoteTerm phi (rSubstList s x A) = substList (denoteTerm phi s) x (map (denoteTerm phi) A).
Proof.
  revert x. induction s; intros;simpl.
  - decide (x < x0); decide (x0 > x); try lia ;intuition (try congruence);simpl.
    now rewrite <-map_nth with (f:= denoteTerm phi).
  -now rewrite IHs1,IHs2.
  -now rewrite IHs.
  -rewrite substList_closed. auto. apply H.
  -rewrite IHs. 2:tauto. reflexivity.
Qed.

Lemma map_ext' : forall (A B : Type) (f g : A -> B) (l:list A),
    (forall a : A, a el l -> f a = g a) ->  map f l = map g l.
Proof.
  intros. induction l.
  -reflexivity.
  -simpl. rewrite H;auto.  f_equal. apply IHl. intros. apply H. auto.
Qed.

Lemma denoteTerm_correct phi s: Proc phi -> deClos (denoteComp phi s) = denoteTerm phi (rDeClos s).
Proof.
  intros pp. unfold denoteComp, rDeClos. pattern s. apply rComp_ind_deep;intros;simpl;try congruence.
  -rewrite rSubstList_correct;auto. f_equal.
   rewrite !map_map. now apply map_ext'.
Qed.

Definition rCompBeta s t :=
  match s,t with
  |rCompClos (rLam ls) A,rCompClos (rLam lt) B => Some (rCompClos ls (t::A))
  |rCompClos (rLam ls) A,rCompClos (rConst x) B => Some (rCompClos ls (t::A))
  |rCompClos (rLam ls) A,rCompClos (rRho lt) B => Some (rCompClos ls (t::A))
  |_,_ => None
  end.


Definition rCompAppCount :=
  fun (j : nat) (u v : nat * rComp) => let (l, u0) := u in let (k, v0) := v in (j + (l + k), u0 v0).

Fixpoint rCompSeval' n (u : nat*rComp) : (nat *rComp)*bool:=
  match n with
    S n =>
    match u with
    | (l, rCompApp s t) =>
      match rCompSeval' n (0,s),rCompSeval' n (0,t) with
        (i, s',true),(j, t',true) =>
        match rCompBeta s' t' with
          Some u => rCompSeval' n ((S l)+(i+j),u)
        | None => ((l+(i+j),s' t'),false)
        end
      | ((i,s'),_),((j,t'),_) => ((l+(i+j),s' t'),false)
      end
    | (l, rCompClos (rApp s t) A ) =>
      rCompSeval' n (l, rCompApp (rCompClos s A) (rCompClos t A))
    | (l , rCompClos (rVar x) A )=> (l,nth x A (rCompVar x),true)
    | (l, rCompClos (rConst x) A )=> (u,true)
    | (l, rCompVar x ) => (u,true)
    | (l, rCompClos (rLam _) A) => (u,true)
    | (l, rCompClos (rRho _) A) => (u,true)
    end
  | 0 => (u,true)
  end.



Definition rCompSeval n u : (nat*rComp):=
  (fst (rCompSeval' n u)).

Lemma rCompBeta_sound phi (s t u: rComp) : Proc phi -> rCompBeta s t = Some u -> denoteComp phi (s t) >[(1)] denoteComp phi u.
Proof with simpl in *;try congruence;auto.
  intros pp eq. destruct s... destruct s... destruct t... destruct s0; inv eq...
  -constructor. apply pp.
  -constructor. eexists. reflexivity.
Qed.


Functional Scheme rCompSeval'_ind := Induction for rCompSeval' Sort Prop.


Lemma rCompSeval_sound n phi s l:
  Proc phi -> let (k,t) := rCompSeval n (l,s) in k >= l /\ denoteComp phi s >[(k-l)] denoteComp phi t.
Proof with (repeat inv_validComp;repeat (eassumption || constructor || intuition|| subst ; eauto using star || rewrite Nat.sub_diag in * || rewrite <- minus_n_O in *||cbn in * )).
  intros. unfold rCompSeval.
  pose (p:= (l,s)).
  change (let (k, t) := fst (rCompSeval' n p) in k >= fst p /\denoteComp phi  (snd p) >[(k-(fst p))] denoteComp phi t).
  generalize p. clear l s p. intros p.
  functional induction (rCompSeval' n p); intros;cbn...
  -rewrite e2,e5 in *...  eapply rCompBeta_sound in e8;try eauto. destruct (rCompSeval' _ (S _,_ ));destruct p... eapply (CPow_trans (t:= denoteComp phi (s' t')))...
  -rewrite e2,e5 in *...  eapply (CPow_trans (t:= denoteComp phi (s' t')))...
  -rewrite e2,e5 in *...  eapply (CPow_trans (t:= denoteComp phi (s' t')))...
  -rewrite e2,e5 in *...  eapply (CPow_trans (t:= denoteComp phi (s' t')))...
  -rewrite <- map_nth...
  -repeat destruct (rCompSeval' _ _)... destruct p... eapply CPow_trans...
Qed.

Lemma rCompBeta_rValidComp s t u phi : rValidComp phi s -> rValidComp phi t -> rCompBeta s t = Some u -> rValidComp phi u.
Proof with repeat (congruence || subst || simpl in * || intuition ).
  unfold rValidComp in *. intros vs vt eq. assert (pp:Proc phi)by (inv vs;auto). split;auto.  unfold rCompBeta in eq. destruct s... destruct s... destruct t... destruct s0...
  -inv eq. inv H0; inv H2. constructor... rewrite map_length in *. now inv H7.
  -inv eq. inv H0; inv H2. constructor...
   +destruct (pp x) as [_ H']. inv H'. now rewrite H0.
   +rewrite map_length in *. now inv H7.
  -inv eq. inv H0; inv H2. constructor...
   +rewrite map_length in *. now inv H7.
   +rewrite map_length in *. now inv H7.
Qed.

Lemma rCompSeval_rValidComp n s phi k : Proc phi -> rValidComp phi s -> rValidComp phi (snd (rCompSeval n (k,s))).
Proof with repeat (eapply validCompApp ||apply validCompClos || congruence || subst || simpl in * || intuition).
  intros P. unfold rCompSeval. revert s k. induction n; intros s k [? vs];(split;[auto|])... destruct s;try now  inv vs;cbn...
  -inv vs. assert (IHn1 := IHn s1 0 ). assert (IHn2 := IHn s2 0).
   unfold snd,fst in *. do 2 destruct ((rCompSeval' n (_,_)))... destruct p,p0... unfold rValidComp in *. destruct b,b0... destruct (rCompBeta r r0) eqn:eq;unfold rValidComp in *.
   +apply IHn... eapply rCompBeta_rValidComp;eauto;  unfold rValidComp in *...
   +idtac...
  -unfold rValidComp in *. inv vs. destruct s;simpl...
   +rewrite <- map_nth. apply H2. apply nth_In. now inv H4.
   +apply IHn;auto. simpl in *. split;auto. inv H4. repeat constructor...
Qed.

Lemma rClosed_valid s phi : Proc phi -> (rClosed phi s <-> rValidComp phi (rCompClos s [])).
Proof.
  intros pp. unfold rClosed. unfold rValidComp. rewrite closed_dcl. split;intros H.
  -repeat constructor;simpl;intuition;apply H0.
  -inv H. inv H1. now tauto.
Qed.



Lemma expandDenote phi s: Proc phi -> denoteTerm phi s = deClos (denoteComp phi (rCompClos s [])).
  intros pp. rewrite (denoteTerm_correct _ pp). simpl. rewrite rSubstList_correct;auto. simpl. now rewrite substList_nil.
Qed.

Lemma rDeClos_reduce  phi s: Proc phi -> rValidComp phi s -> deClos (denoteComp phi s) = deClos (denoteComp phi (rCompClos (rDeClos s) [])).
Proof.
  intros pp vc. simpl. rewrite <- denoteTerm_correct;auto. now rewrite substList_nil.
Qed.


Lemma rDeClos_rValidComp phi s: Proc phi -> rValidComp phi s -> rValidComp phi (rCompClos (rDeClos s) []).
Proof with repeat (eauto || congruence || subst || simpl in * || intuition).
  intros pp [? H]. unfold rValidComp in *. split;try tauto.  simpl. apply deClos_valComp in H. apply validComp_closed. now rewrite <- denoteTerm_correct.
Qed.


Lemma rStandardize n phi s : Proc phi -> rClosed phi s -> let (l,s') := (rCompSeval n (0,rCompClos s [])) in  rPow phi l s (rDeClos s').
Proof with eauto.
  intros pp cl. unfold rPow. rewrite rClosed_valid in *;auto. assert (cl': rValidComp phi (snd (rCompSeval n (0,rCompClos s [])))).
  -apply rCompSeval_rValidComp;auto.
  - destruct rCompSeval eqn:eq1. rewrite !expandDenote;auto.  specialize (rCompSeval_sound n (rCompClos s []) 0 pp);intros  H. rewrite eq1 in H.
    destruct H as [_ H]. rewrite <- minus_n_O in H. rewrite <- rDeClos_reduce... apply deClos_correct... destruct cl...
Qed.

Lemma rStandardizeUsePow n phi s:
  Proc phi -> rClosed phi s ->
  let (l,s') := (rCompSeval n (0,rCompClos s [])) in denoteTerm phi s >(l) denoteTerm phi (rDeClos s').
Proof.
  apply rStandardize.
Qed.

Lemma rStandardizeUse n phi s:
  Proc phi -> rClosed phi s ->
  let (l,s') := (rCompSeval n (0,rCompClos s [])) in denoteTerm phi s >* denoteTerm phi (rDeClos s').
Proof.
  intros a b.
  specialize (rStandardizeUsePow n a b). destruct (rCompSeval _ _). rewrite star_pow. firstorder.
Qed.


Fixpoint rClosed_decb' n u : bool:=
  match u with
  | rApp s t => andb (rClosed_decb' n s) (rClosed_decb' n t)
  | rVar x => negb (leb n x)
  | rConst x => true
  | rLam s =>rClosed_decb' (S n) s
  | rRho s =>rClosed_decb' (S n) s
  end.

Lemma rClosed_decb'_correct s phi n: Proc phi -> rClosed_decb' n s = true -> bound n (denoteTerm phi s).
Proof.
  intros pp. revert n. induction s;intros n eq;simpl in *.
  -rewrite Bool.negb_true_iff in eq. apply leb_complete_conv in eq. now constructor.
  -rewrite Bool.andb_true_iff in eq. constructor; intuition.
  -constructor. auto.
  -apply bound_ge with (k:=0);[|lia]. rewrite <- closed_dcl. apply pp.
  -unfold rho,r.
   repeat (eapply dclApp||eapply dcllam||eapply dclvar).
   all:try lia. eauto.
Qed.

Definition rClosed_decb s:= rClosed_decb' 0 s.

Lemma rClosed_decb_correct phi s : Proc phi -> rClosed_decb s = true -> rClosed phi s.
Proof.
  intros. hnf;split;[auto|]. rewrite closed_dcl. apply rClosed_decb'_correct;auto.
Qed.

(* Facts about denote *)

Definition liftPhi Vars n:=nth n Vars I.

Arguments liftPhi Vars n/.

Lemma liftPhi_correct Vars: (forall s, s el Vars -> proc s) -> Proc (liftPhi Vars).
Proof.
  intros H n. unfold liftPhi. destruct (nth_in_or_default n Vars I) as [?|eq].
  -now apply H.
  -rewrite eq. cbv. split.  auto. eexists. eauto.
Qed.


Fixpoint benchTerm x : rTerm :=
  match x with
    0 => (rLam (rVar 0))
  | S x => (rLam (benchTerm x)) (rLam (rVar 0))
  end.

Close Scope LClos.
