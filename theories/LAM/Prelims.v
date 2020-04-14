Require Export Undecidability.LAM.BaseExtension Coq.Program.Basics PslBase.Base.
From Undecidability.L Require Export Prelim.ARS L.
Export ARSNotations.

Definition evaluatesIn (X : Type) (R : X -> X -> Prop) n (x y : X) := pow R n x y /\ terminal R y.

Inductive evalIn : nat -> term -> term -> Prop :=
  evalInVal s : evalIn 0 (lam s) (lam s)
| evalInBeta (s s' t t' u : term) i j k l: evalIn i s (lam s') -> evalIn j t (lam t') -> evalIn k (subst s' 0 (lam t')) u -> l = (i+j+1+k) -> evalIn l (s t) u.


Lemma step_evaluatesIn s s' t k: s ≻ s' -> evalIn k s' t -> evalIn (S k) s t.
Proof.
  intros H; induction H in t,k|-*; intros;  try inv H0; eauto 20 using evalIn.
  eapply IHstep in H4. econstructor; eauto. omega. 
Qed.

Lemma evalIn_correct s t k:
  (evalIn k s t <-> pow step k s t /\ lambda t).
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
    eapply pow_step_congL;now eauto.
    eapply pow_add.
    eexists;split.
    eapply pow_step_congR;now eauto.
    eapply pow_add.
    eexists;split.
    eapply (rcomp_1 step). eauto.
    eauto. 
  -intros [R lt].
   induction k in s,t,R,lt,R|-*.
   +inv R. inv lt. constructor.
   +change (S k) with (1+k) in R. eapply pow_add in R as (?&R'&?).
    eapply (rcomp_1 step) in R'. eapply step_evaluatesIn;eauto 10.
Qed.


Reserved Notation "s '>>lm' t" (at level 50).

Inductive lm_step : term -> term -> Prop :=
| lstepApp  s t     : app (lam s) (lam t) >>lm subst s 0 (lam t)
| lstepAppR s t  t' : t >>lm t' -> app (lam s) t >>lm app (lam s) t'
| lstepAppL s s' t  : s >>lm s' -> app s t >>lm app s' t
where "s '>>lm' t" := (lm_step s t).
Hint Constructors lm_step : core.

(** * Properties of star: *)

Instance pow_lm_step_congL k:
  Proper ((pow lm_step k) ==> eq ==> (pow lm_step k)) app.
Proof.
  intros s t R u ? <-. revert s t R u.
  induction k;cbn in *;intros ? ? R ?. congruence. destruct R as [s' [R1 R2]].
  exists (s' u). firstorder.
Defined.

Instance pow_lm_step_congR k:
  Proper (eq ==>(pow lm_step k) ==> (pow lm_step k)) (fun s t => app (lam s) t).
Proof.
  intros s ? <- t u R. revert s t u R.
  induction k;cbn in *;intros ? ? ? R. congruence. destruct R as [t' [R1 R2]].
  exists (lam s t'). firstorder.
Defined.



Lemma lm_step_evaluatesIn s s' t k: s >>lm s' -> evalIn k s' t -> evalIn (S k) s t.
Proof.
  intros H; induction H in t,k|-*; intros.
  all:try inv H0; eauto 20 using evalIn.
  eapply IHlm_step in H4. econstructor; eauto. omega. 
Qed.

Lemma lm_evalIn_correct s t k:
  (evalIn k s t <-> pow lm_step k s t /\ lambda t).
Proof.
  split.
  -intros R.
   induction R.
   +unfold pow;cbn. eauto.
   +destruct IHR1. 
    destruct IHR2.
    destruct IHR3.
    split;[|assumption].
    subst l.
    replace (i+j+1+k) with (i+(j+(1+k))) by omega. 
    eapply pow_add.
    eexists;split.
    eapply pow_lm_step_congL;now eauto.
    eapply pow_add.
    eexists;split.
    eapply pow_lm_step_congR;now eauto.
    eapply pow_add.
    eexists;split.
    eapply (rcomp_1 lm_step). eauto.
    eauto. 
  -intros [R lt].
   induction k in s,t,R,lt,R|-*.
   +inv R. inv lt. constructor.
   +change (S k) with (1+k) in R. eapply pow_add in R as (?&R'&?).
    eapply (rcomp_1 lm_step) in R'. eapply lm_step_evaluatesIn;eauto 10.
Qed.

(* space in LM-reduction *)
Inductive evalSpace : nat -> term -> term -> Prop :=
  evalSpaceVal s : evalSpace (size (lam s)) (lam s) (lam s)
| evalSpaceBeta (s s' t t' u : term) m1 m2 m3 m:
    evalSpace m1 s (lam s') ->
    evalSpace m2 t (lam t') ->
    evalSpace m3 (subst s' 0 (lam t')) u -> m = max (m1 + 1 + size t)
                                                 (max (size (lam s') + 1 + m2)
                                                      (max (1 + size (lam s')+size(lam t')) m3)) ->
    evalSpace m (s t) u.

Lemma evalSpace_ge s t m: evalSpace m s t -> size s<= m /\ size t <= m.
Proof.
  induction 1. omega.
  subst m. cbn -[plus]. all:(repeat apply Nat.max_case_strong;try omega).
Qed.

(* Lemma step_evaluatesSpace s s' t m: s >>lm s' -> evalSpace m s' t -> evalSpace (max (size s) m) s t. *)
(* Proof. *)
(*   intros H; induction H in t,m|-*; intros H'. *)
(*   -inv H'. *)
(*    +destruct s;inv H1. decide _;inv H0. *)
(*     all:repeat econstructor. *)
(*     all:cbn -[plus]. *)
(*     all:(repeat apply Nat.max_case_strong;try omega). *)
(*    +destruct s;inv H. now decide _. *)
(*     econstructor. 1,2:econstructor. cbn. *)
(*     econstructor. *)
(*     1-4:now eauto. *)
(*     cbn -[plus].  *)
(*     (repeat apply Nat.max_case_strong;intros;try omega). *)
(*   -inv H'. inv H2. *)
(*    specialize (evalSpace_ge H3) as [? ?]. *)
(*    apply IHlm_step in H3. *)
(*    specialize (evalSpace_ge H5) as [? ?]. *)
(*    specialize (evalSpace_ge H3) as [_ H7]. *)
(*    econstructor;[now eauto using evalSpace..|].  *)
(*    revert H7. cbn -[plus] in *.  *)
(*    (repeat apply Nat.max_case_strong;intros;try omega). *)
(*   -inv H'. *)
(*    specialize (evalSpace_ge H2) as [? ?]. *)
(*    eapply IHlm_step in H2. *)
(*    specialize (evalSpace_ge H2) as [_ H7]. *)
(*    specialize (evalSpace_ge H3) as [? ?]. *)

(*    econstructor. *)
(*    1-3:eassumption. *)
(*    revert H7. *)
(*    cbn -[plus] in *.  *)
(*    (repeat apply Nat.max_case_strong;intros;try omega). *)
(* Qed. *)


Inductive starWith {X} (R:X -> X -> Prop) P : X -> X -> Prop:=
  starWithR x: P x -> starWith R P x x
| starWithC x y z: R x y -> P x -> starWith R P y z -> starWith R P x z.

Lemma starWith_sub X R (P P' : X->Prop) : (forall x, P x -> P' x) -> starWith R P <=2 starWith R P'.
Proof.
  induction 2;eauto using starWithR,starWithC. 
Qed.

Definition relWith {X} (R:X->X->Prop) P := fun x y => R x y /\ P x /\ P y.

Lemma relWith_sub X R (P P' : X->Prop) : (forall x, P x -> P' x) -> relWith R P <=2 relWith R P'.
Proof.
  unfold relWith. intuition. 
Qed.

Definition star_space m' := starWith lm_step (fun s => size s <= m').

Instance starWith_trans A (R : A -> A -> Prop) P: Transitive (starWith R P).
Proof.
  induction 1;intros. eauto. econstructor;eauto.
Qed.
  

Lemma star_space_congL m m' s s' t:
  star_space m s s' -> m' = (1 + m + size t) -> star_space m' (s t) (s' t).
Proof.
  intros R Heq. unfold star_space in *.
  induction R as [s | s ? s'].
  -apply starWithR. cbn. omega. 
  -eapply starWithC. eauto using lm_step. now cbn;omega. eauto.
Defined.

Lemma star_space_congR m m' s t t':
  star_space m t t' -> m' = (1 + m + size (lam s)) -> star_space m' (lam s t) (lam s t').
Proof.
  intros R Heq.  unfold star_space in *.
  induction R as [t | t ? t'].
  -apply starWithR. cbn in *. omega. 
  -eapply starWithC. eauto using lm_step. now cbn in *;omega. eauto.
Defined.

(* Lemma lm_evaSpace_correct s t m: *)
(*   (exists m', m' <= m /\ evalSpace m' s t) <->  *)
(*    star_space m s t /\ lambda t. *)
(* Proof. *)
(*   split. *)
(*   -intros (m'&leq&R). *)
(*    enough (star_space m' s t /\ lambda t) as (H&?). *)
(*    {split. 2:now eauto. eapply starWith_sub. 2:eassumption. cbn. intros;omega. } *)
(*    clear m leq. *)
(*    induction R. *)
(*    +repeat econstructor. *)
(*    +destruct IHR1 as (R1'&?).  *)
(*     destruct IHR2 as (R2'&?). *)
(*     destruct IHR3 as (R3'&?). *)
(*     split;[|firstorder]. *)
(*     subst m. *)
(*     transitivity ((lam s') t). *)
(*     {eapply starWith_sub. 2:now eapply star_space_congL;eauto. *)
(*      cbn - [size max]. intros. repeat eapply Nat.max_case_strong; omega. } *)
(*     transitivity ((lam s') (lam t')). *)
(*     {eapply starWith_sub. 2:now eapply star_space_congR;eauto. *)
(*      cbn - [size max]. intros. repeat eapply Nat.max_case_strong; omega. } *)
(*     eapply starWithC. now constructor. *)
(*     {cbn - [max]. repeat eapply Nat.max_case_strong; omega. } *)
(*     eapply starWith_sub. 2:eassumption. *)
(*     cbn - [max]. intros; repeat eapply Nat.max_case_strong; omega. *)
(*   -intros (R&H). *)
(*    induction R as [t | s s' t];inv H;rename x into t. *)
(*    +eauto using evalSpace. *)
(*    +destruct IHR as (m'&leq&R2);[now eauto|]. *)
(*     eexists. split. *)
(*     2:{ eapply step_evaluatesSpace. all:eassumption. } *)
(*     eapply Nat.max_case_strong; omega. *)
(* Qed. *)


(** Strong normalisation *)

Lemma star_impl X (R1 R2: X -> X->Prop): R1 <=2 R2 -> star R1 <=2 star R2.
Proof.
  induction 2;eauto using star.
Qed.

Definition simulatedWith {X Y} (stepX: X -> X -> Prop) (stepY: Y -> Y -> Prop) (sim:X -> Y -> Prop)
  := forall x1 x2 y1, sim x1 y1 -> stepX x1 x2 -> exists y2, sim x2 y2 /\ stepY y1 y2.

Lemma simulatesStar X Y stepX stepY (sim: X -> Y -> Prop) :
  simulatedWith stepX (star stepY) sim -> simulatedWith (star stepX) (star stepY) sim.
Proof.
  intros sims x1 x2 y1 S1 R1. induction R1 in y1,S1|-*.
  -eauto using star.
  -destruct (sims _ _ _ S1 H) as (y'&S'&R').
   destruct (IHR1 _ S') as (y2&S2&R2).
   rewrite R2 in R'. eauto. 
Qed.

Lemma simulatedWith_weaken X Y stepX (stepY stepY':_->_->Prop) (sim: X -> Y -> Prop) :
  simulatedWith stepX stepY sim -> stepY <=2 stepY' -> simulatedWith stepX stepY' sim.
Proof.
  intros H. repeat intro. edestruct H as (?&?&?). all:eauto. 
Qed.

Lemma simulatedWithStar X Y stepX (stepY:_->_->Prop) (sim: X -> Y -> Prop) :
  simulatedWith stepX stepY sim -> simulatedWith (star stepX) (star stepY) sim.
Proof.
  intros H. eapply simulatesStar. eapply simulatedWith_weaken. all:eauto using star. 
Qed.

Inductive stutterStep Y (P:Y->Prop) (step:Y->Y->Prop) :Y->Y->Prop :=
  stutterStepR y: P y -> stutterStep P step y y
| stutterStepStutter y1 y1' y2 : P y1 -> step y1 y1' -> stutterStep P step y1' y2 -> stutterStep P step y1 y2.

Lemma stutterStep_star Y (P:Y->Prop) step : stutterStep P step <=2 (fun x y => star step x y /\ P y /\ P x).
Proof.
  intros ? ? R. induction R;[|destruct IHR as (?&?&?)];eauto using star.
Qed.

Definition stutterSimulatedWith {X Y} (stepX: X -> X -> Prop) (stepY: Y -> Y -> Prop) (sim:X -> Y -> Prop)
  := forall x1 x2 y1, sim x1 y1 -> stepX x1 x2 -> sim x2 y1 \/ exists y1' y2, sim x2 y2 /\ stutterStep (sim x1) stepY y1 y1' /\ stepY y1' y2.

Definition stutterTerminal Y P stepY (y:Y):= exists y', stutterStep P stepY y y' /\ terminal stepY y'.

Definition stutterTerminalSensitive X Y stepX stepY (sim :X->Y->Prop) :=
  forall x y, sim x y -> terminal stepX x -> stutterTerminal (sim x) stepY y.

Definition star_preserves X (R:X->X-> Prop) (P:X->Prop):
  (forall X X', R X X' -> P X -> P X') -> forall X X', star R X X' -> P X -> P X'.
Proof.
  intros H ? ? R'. induction R';eauto. 
Qed.


Lemma simulatedEvaluates X Y stepX stepY (sim : X -> Y -> Prop): stutterSimulatedWith stepX stepY sim -> stutterTerminalSensitive stepX stepY sim ->
simulatedWith (evaluates stepX) (evaluates stepY) sim.
Proof.
  intros sims ter x1 x2 y1 S (R&T). 
  assert (stutterStep (flip sim y1) stepX x1 x1) as R' by eauto using stutterStep.
  revert y1 R' S. generalize x1 at 2. induction R; intros ? ? ? ?.  (* in x1 y2. in T,S,y1|-*.  ;intros y1 x0 S R0. *)
  -apply stutterStep_star in R' as (?&?&?). (*apply stutterStep_star in R0 as (?&?&?).*)
    eapply ter in T as (?&R'&T').

    2:eassumption.
   apply stutterStep_star in R' as (?&?&?).
   unfold evaluates;eauto.
  -apply stutterStep_star in R' as (?&?&?).
    eapply sims in H as [|(?&?&?&?&?)]. 3:eassumption.
   +edestruct IHR. all:eauto using stutterStepR.
   +edestruct IHR. 1-3:eauto using stutterStep. unfold evaluates in *.
    apply stutterStep_star in H3 as (?&?&?).
    eexists. 
    rewrite H3. rewrite (R_star H4). eauto. 
Qed.

Reserved Notation "s '>>lm' t" (at level 50).

Lemma lam_terminal u: lambda u -> terminal step u.
Proof.
  intros H ? R;inv H;inv R.  
Qed.

Lemma functional_lm_step : functional lm_step.
Proof.
  intros ? ? u R1 R2;induction R1 in u,R2|-*.
  -inv R2. congruence. all:inv H2.
  -inv R2. inv R1. all:now erewrite IHR1;eauto.
  -inv R2. inv R1. inv R1. erewrite IHR1;eauto.
Qed.

Lemma functional_uniform_confluent X (R:X->X->Prop): functional R -> uniform_confluent R.
Proof.
  intros F ? ? ? R1 R2. left. eapply F;eauto.
Qed.


Lemma complete_induction (p : nat -> Prop) : (forall x0 : nat, (forall y : nat, y < x0 -> p y) -> p x0) -> forall x, p x.
Proof. (*usable as induction scheme*)
  intros. now apply (complete_induction x).
Qed.



Instance le_preorder : PreOrder le.
Proof.
  constructor. all:cbv. all:intros;omega. 
Qed.

Instance S_le_proper : Proper (le ==> le) S.
Proof.
  cbv. fold plus. intros. omega.
Qed.

Instance plus_le_proper : Proper (le ==> le ==> le) plus.
Proof.
  cbv. fold plus. intros. omega.
Qed.

Instance mult_le_proper : Proper (le ==> le ==> le) mult.
Proof.
  cbv. intros. 
  apply mult_le_compat. all:eauto. 
Qed.
