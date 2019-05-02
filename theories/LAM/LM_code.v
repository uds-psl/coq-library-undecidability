From Undecidability.L Require Import L.
From Undecidability.LAM Require Import Prelims LM AbstractSim.
(** * Verification with Parallel Substitution *)
(** * Machine and Compiler *)

Inductive clos :=  closC (c:Pro) (E : list clos).

Notation "c / E" := (closC c E).

Definition tailRecursion c E T: list clos :=
  match c with
    [] => T
  |  _ => (c/ E)::T
  end.

Lemma tailRecursion_compile s c E C: tailRecursion (compile s++c) E C = ((compile s++c)/ E::C).
Proof.
  induction s in c|-*;cbn. all:cbn;autorewrite with list in *;try congruence.
Qed. 

Definition state := (list clos *list clos)%type.
Hint Transparent state.

Inductive step : state -> state -> Prop:=
| step_betaC P E T p Q E' V:
    step ( (appT::P)/E :: T,p :: Q/E' ::V) (Q/(p::E') :: tailRecursion P E T,V)
| step_pushVal  P P' Q E T V:
     jumpTarget 0 [] P = Some (Q,P') -> step ((lamT::P)/E ::T,V) (tailRecursion P' E T,Q/E::V)
| step_load P E x V g T:
    nth_error E x = Some g ->
    step ((varT x::P)/E::T,V) (tailRecursion P E T,g::V).

Hint Constructors step.

(** * Verification *)
(** Parallel substitution with a list*)
Fixpoint psubst (s:term) (k:nat) (A: list term): term :=
  match s with
  | var n => if Dec (k>n) then var n else match nth_error A (n-k) with Some s => s | _ =>  (var n) end
  | app s t => (psubst s k A) (psubst t k A)
  | lam s => lam (psubst s (S k) A)
  end.

Inductive representsValue : clos -> term -> Prop :=
  representsValueC E Env s:
    Forall2 representsValue E Env
    -> bound (length E) (lam s)
    -> representsValue (compile s/E) (lam (psubst s 1 Env)).

Hint Constructors representsValue.

Lemma psubst_nil s k: psubst s k [] = s.
Proof.
  revert k;induction s;cbn;intros;try congruence.
  decide _. tauto. destruct _ eqn:eq. apply nth_error_Some_lt in eq;cbn in *;omega.  tauto. 
Qed.

Lemma psubst_cons x s t A: Forall closed A -> subst (psubst s (S x) A) x t = psubst s x (t::A).
Proof.
  revert x;induction s;simpl;intros x cl.
  - decide (S x > n);simpl. decide (x>n); destruct (Nat.eqb_spec n x);try omega;try tauto. subst. now rewrite minus_diag. decide (x>n). omega. destruct (n-x) eqn: eq. omega. assert (n2=n-S x) by omega. subst n2. cbn. edestruct nth_error eqn:eq'.
   +apply bound_closed. rewrite Forall_forall in cl. eapply closed_dcl. apply cl;eauto using nth_error_In.
   +cbn. destruct (Nat.eqb_spec n x). omega. congruence. 
  -now rewrite IHs1,IHs2.
  -rewrite IHs. all:tauto.  
Qed.

Lemma psubst_is_bound y A s: Forall closed A -> bound (y+|A|) (s) -> bound y (psubst s y A).
Proof.
  intros vA. revert y. induction s;intros y dA.
  -cbn. decide _. econstructor. eauto. edestruct nth_error_lt_Some as [s eq];[|rewrite eq]. inv dA. omega.
   rewrite Forall_forall in vA. eapply bound_ge. eapply closed_dcl. eapply vA. 2:omega. eauto using nth_error_In.
  -inv dA. simpl. constructor;auto.
  -simpl. constructor. apply IHs. now inv dA.
Qed.


(** *** Deep induction lemmas *) 
Definition clos_ind_deep'
           (P : clos -> Prop) (Pl : list clos -> Prop)
           (IHClos : forall (p : Pro) (E : list clos), Pl E -> P (closC p E))
           (IHNil : Pl nil) (IHCons : forall (a:clos) (E : list clos), P a -> Pl E -> Pl (a::E))
           (x:clos) : P x :=
  (fix f c : P c:=
     match c with
     | closC s E =>
       IHClos s E
              ((fix g E : Pl E := 
                  match E with
                    [] => IHNil
                  | a::E => IHCons a E (f a) (g E)
                  end) E)
     end) x
.

Definition clos_ind_deep
           (P : clos -> Prop)
           (IHClos : forall (s : Pro) (E: list clos),
                       Forall P E -> P (closC s E)) : forall x, P x.
Proof.
  apply clos_ind_deep' with (Pl:=Forall P);auto.
Qed.

Lemma representsValue_closed p s : representsValue p s -> closed s .
Proof.
  induction p in s|-* using clos_ind_deep. intros cl;inv cl. eapply closed_dcl. econstructor. eapply psubst_is_bound. 2:inv H4;erewrite <-Forall2_length;now eauto.
  eapply Forall_forall. intros ? xel.  eapply In_nth_error in xel as (?&?).
  edestruct Forall2_nth2 as (?&?&?). 1-2:now eauto. 
   eapply Forall_nth in H. 2:eauto. now apply H. 
Qed.

Lemma representsValue_closedEnv E Env : Forall2 representsValue E Env -> Forall closed Env.
Proof.
  intros. 
  eapply Forall_forall. intros ? xel.  eapply In_nth_error in xel as (?&?).
  edestruct Forall2_nth2 as (?&?&?). all:eauto using  representsValue_closed.
Qed.


Lemma completeness' s t c0 C V E Env:
  Forall2 representsValue E Env
  -> bound (length E) s
  -> eval (psubst s 0 Env) t -> 
  exists p, representsValue p t /\ star step ((compile s++c0)/E::C,V) (tailRecursion c0 E C,p::V).
Proof.
  intros repE dcl Ev.
  remember (psubst s 0 Env) as s' eqn:eq.
  induction Ev in s,c0,E,Env,C,V,repE,eq,dcl |- *.
  - destruct s;inv eq.
(*    +rewrite <- minus_n_O in H0. destruct _ eqn:eq;[|now inv H0]. subst t. *)
(*     edestruct Forall2_nth2 as (p&?&?);eauto. *)
(*     exists p. cbn. eauto using R_star. *)
(*    +eexists;split. eauto. *)
(*     eapply R_star. cbn. *)
(*     autorewrite with list. *)
(*     cbn. constructor. apply jumpTarget_correct. *)
(*   -destruct s; inv eq. *)
(*    +exfalso. destruct _ eqn:eq;inv H0. edestruct Forall2_nth2 as (p&?&?);eauto. inv H0. *)
(*    +cbn. autorewrite with list. cbn. *)
(*     inv dcl. *)
(*     edestruct IHEv1 as (p1&rep1&R1). *)
(*     1-3: try reflexivity;now eauto. *)
(*     inv rep1. *)
(*     edestruct IHEv2 as (p2&rep2&R2). *)
(*     1-3: try reflexivity;now eauto. *)
(*     inv rep2. *)
(*     edestruct IHEv3 with (c0:=@nil Tok)  as (p3&rep3&R3). *)
(*     3: now rewrite <-psubst_cons;eauto using representsValue_closedEnv. *)
(*     now eauto. *)
(*     now inv H4. *)
    
(*     exists p3. split. now eauto. *)
(*     inv rep3. *)
(*     rewrite R1,tailRecursion_compile,R2. cbn. *)
(*     eapply starC. unfold tailRecursion. now eauto. *)
(*     autorewrite with list in R3. *)
(*     exact R3. *)
(* Qed. *)
Admitted.

Definition init s :state := ([compile s/[]],[]).

Lemma completeness s t:
  closed s ->
  eval s t -> 
  exists p, representsValue p t /\ star step ([(compile s)/[]],[]) ([],[p]).
Proof.
  intros cls Ev.
  rewrite closed_dcl in cls.
  specialize completeness' with (V:=[]) (E:=[]) (C:=[]) (c0:=[]) (2:=cls) as (p&rep&R).
  1:now constructor. 
  Focus 1. { rewrite psubst_nil. exact Ev. } Unfocus. 
  cbn in R. autorewrite with list in R. 
  exists p. eauto.
Qed.


