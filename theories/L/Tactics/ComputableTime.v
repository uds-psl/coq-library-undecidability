From Undecidability.L Require Export Tactics.Computable.

(** ** Time bounds *)

Fixpoint timeComplexity t (tt: TT t) : Type :=
  match tt with
    ! _ => unit
  | @TyArr t1 t2 tt1 tt2 => t1 -> timeComplexity tt1 -> (nat*timeComplexity tt2)
  end.

Arguments timeComplexity : clear implicits.
Arguments timeComplexity _ {_}.

Fixpoint computesTime {t} (ty : TT t) :  forall (x:t) (xInt :term) (xTime :timeComplexity t), Type :=
  match ty with
    !_ => fun x xInt _=> xInt = enc x
  | @TyArr t1 t2 tt1 tt2 =>
    fun f fInt fTime =>
      proc fInt * 
      forall (y : t1) yInt (yTime:timeComplexity t1),
        computesTime y yInt yTime
        -> let fyTime := fTime y yTime in
          {v : term & (redLe (fst fyTime) (fInt yInt) v) * computesTime (f y) v (snd fyTime)}
  end%type.

Arguments computesTime {_} _ _ _ _.

Class computableTime {X : Type} (ty : TT X) (x : X) evalTime: Type :=
  {
    extT : extracted x;
    extTCorrect : computesTime ty x extT evalTime
  }.

Existing Instance extT|4.

Hint Mode computableTime + - + -: typeclass_instances. (* treat argument as input and force evar-freeness*)

Global Arguments computableTime {X} {ty} x.
Global Arguments extT {X} {ty} x {_ computableTime} : simpl never.
Global Arguments extTCorrect {X} ty x {_ computableTime} : simpl never.
Definition evalTime X ty x evalTime (computableTime : @computableTime X ty x evalTime):=evalTime.
Global Arguments evalTime {X} {ty} x {evalTime computableTime}.

(** A Notation to allow inference of the TT parameter for function types. Coq checks that functions only appear at positions where functions are allowed before it inferes holes, so t complains that f "is a product while it is expected to be '@timeComplexity (forall _ : _, _) ?ty'". *)
Notation "'computableTime'' f" := (@computableTime _ ltac:(let t:=type of f in refine (_ : TT t);exact _) f) (at level 0,only parsing).

Local Fixpoint notHigherOrder t (ty : TT t) :=
  match ty with
    TyArr (TyB _) ty2 => notHigherOrder ty2 
  | TyB _ => True
  | _ => False
  end.

Local Lemma computesTime_computes_intern s t (ty: TT t) f evalTime:
  notHigherOrder ty -> computesTime ty f s evalTime -> computes ty f s.
Proof.
  revert s f.
  induction ty;intros s f H int. 
  - exact int. 
  -destruct ty1; cbn in H. 2:tauto.
   clear IHty1.
   cbn. destruct int as [ps ints]. cbn in ints.
   split. tauto.
   intros. subst.
   edestruct (ints a _ tt eq_refl) as(v&R'&?).
   exists v. split. eapply redLe_star_subrelation. all:eauto.
Defined.

Lemma computableTime_computable X (ty : TT X) (x:X) fT :
  notHigherOrder ty -> computableTime x fT -> computable x.
Proof.
  intros H I. eexists (extT x). destruct I. eapply computesTime_computes_intern. all:eauto.
Defined.

Hint Extern 10 (@computable ?t ?ty ?f) =>
(solve [let H:= fresh "H" in eassert (H : @computableTime t ty f _) by exact _;
                        ( (exact (computableTime_computable (ty:=ty) Logic.I H))|| idtac "Can not derive computable instance from computableTime for higher-order-function" f)]): typeclass_instances.

Lemma computesTimeProc t (ty : TT t) (f : t) fInt fT:
  computesTime ty f fInt fT-> proc fInt.
Proof.
  destruct ty.
  -intros ->. unfold enc. now destruct R. 
  -now intros [? _].
Qed.

Lemma proc_extT {X : Type} (ty : TT X) (x : X) fT ( H : computableTime x fT) : proc (extT x).
Proof.
  unfold extT. destruct H as [? H]. now eapply computesTimeProc in H.
Qed.

Instance reg_is_extT ty (R : registered ty) (x : ty): computableTime x tt.
Proof.
  exists (enc x). split;constructor. 
Defined.

Lemma computesTimeTyB (t:Type) (x:t) `{registered t}: computesTime (TyB t) x (extT x) tt.
Proof.
  unfold extT. now destruct H.
Qed.

Instance extTApp' t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) fT xT (Hf : computableTime f fT) (Hx : computableTime x xT) : computableTime (f x) (snd (fT x xT)).
Proof. 
  destruct Hf as [fInt H], Hx as [xInt xInts].
  eexists (projT1 ((snd H) x xInt xT xInts)). 
  destruct H as [p fInts]. cbn in *. 
  destruct (fInts x xInt xT xInts) as (v&E&fxInts). 
  eassumption. 
Defined.

Lemma extTApp t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) fT xT (Hf : computableTime f fT) (Hx : computableTime x xT) :
  (extT f) (extT x) >(<= fst (evalTime f x (evalTime x))) extT (f x).
Proof.
  unfold extT.
  destruct Hf as [fInt [fP fInts]], Hx as [xInt xInts]. cbn.
  destruct (fInts x xInt xT xInts) as (v&E&fxInts). apply E.
Qed.

Lemma extT_is_enc t1 (R:registered t1) (x: t1) xT (Hf : computableTime x xT) :
  @extT _ _ x xT Hf = enc x.
Proof.
  unfold extT. 
  destruct Hf. assumption.
Defined.

Lemma computesTimeTyArr_helper t1 t2 (tt1 : TT t1) (tt2 : TT t2) f fInt time fT:
  proc fInt
  ->
  (forall (y : t1) yT,
      (time y yT<= fst (fT y yT)) * 
  forall (yInt : term),
    computesTime tt1 y yInt yT
    -> {v : term & evalLe (time y yT) (fInt yInt) v * (proc v -> computesTime tt2 (f y) v (snd (fT y yT)))})%type
-> computesTime (tt1 ~> tt2) f fInt fT.
Proof.
  intros H0 H. split. tauto.
  intros y yInt yT yInts.
  specialize (H y yT) as (lt&H).
  edestruct H as (v&E&Hv). eassumption.
  exists v.
  split. rewrite <- lt. now apply E. 
  apply Hv.
  apply evalLe_eval_subrelation in E. split. rewrite <- E. apply app_closed. apply H0. apply computesTimeProc in yInts. apply yInts. apply E. 
Qed.

Definition computesTimeIf {t} (ty : TT t) (f:t) (fInt : term) (P:timeComplexity t-> Prop) : Type :=
  forall fT, P fT -> computesTime ty f fInt fT.
Arguments computesTimeIf {_} _ _ _ _.


Lemma computesTimeIfStart t1 (tt1 : TT t1) (f : t1) (fInt : term) P fT:
  computesTimeIf tt1 f fInt P -> P fT -> computesTime tt1 f fInt fT.
Proof.
  intros ?. cbn. eauto.
Qed.

Definition computesTimeExp {t} (ty : TT t) (f:t) (s:term) (i:nat) (fInt : term) (fT:timeComplexity t) : Type :=
  evalLe i s fInt * computesTime ty f fInt fT.

Arguments computesTimeExp {_} _ _ _ _ _ _.
  
Lemma computesTimeExpStart t1 (tt1 : TT t1) (f : t1) (fInt : term) fT:
  proc fInt ->
  {v :term & computesTimeExp tt1 f fInt 0 v fT}  -> computesTime tt1 f fInt fT.
Proof.
  intros ? (?&[e lam]&?). decide (fInt=x). subst x. assumption.
  edestruct n. destruct e as ([]&?&?). assumption. inv H0. 
Qed.

Lemma computesTimeExpStep t1 t2 (tt1 : TT t1) (tt2 : TT t2) (f : t1 -> t2) (s:term) k k' fInt fT:
  k' = k -> evalIn k' s fInt -> closed s -> 
  (forall (y : t1) (yInt : term) yT, computesTime tt1 y yInt yT
                                -> {v : term & computesTimeExp tt2 (f y) (s yInt) (fst (fT y yT) +k) v (snd (fT y yT))}%type) ->
  computesTimeExp (tt1 ~> tt2) f s k fInt fT.

Proof.
  intros -> (R1&p1) ? H. split. split. eexists;split. 2:eassumption. omega. tauto. split. split. 2:tauto. rewrite <- R1. tauto. 
  intros y yInt yT yInted.
  edestruct (H y yInt yT yInted) as (v&H2&?).
  eexists v. split.
  edestruct (evalLe_trans_rev) as (H3&R3). exact H2. apply pow_step_congL. eassumption. reflexivity.
  destruct fT. cbn in *. replace (n+k-k) with n in R3 by omega. apply R3. tauto. 
Qed.


Lemma computesTimeExt X (tt : TT X) (x x' : X) s fT:
  extEq x x' -> computesTime tt x s fT -> computesTime tt x' s fT.
Proof.
  induction tt in x,x',s,fT |-*;intros eq.
  -inv eq. tauto.
  -cbn in eq|-*. intros [H1 H2]. split. 1:tauto.
   intros y t yT ints.
   specialize (H2 y t yT ints ) as (v&R&H2).
   exists v. split. 1:assumption.
   eapply IHtt2. 2:now eassumption.
   apply eq.
Qed.

Lemma computableTimeExt X (tt : TT X) (x x' : X) fT:
  extEq x x' -> computableTime x fT -> computableTime x' fT.
  intros ? [s ?]. eexists. eauto using computesTimeExt.
Defined.

Fixpoint changeResType_TimeComplexity t1 (tt1 : TT t1) Y {R: registered Y} {struct tt1}:
  forall (fT: timeComplexity t1) , @timeComplexity _ (projT2 (changeResType tt1 (TyB Y))):= (
  match tt1 with
    @TyB t1 tt1 => fun fT => fT
  | TyArr tt11 tt12 => fun fT x xT => (fst (fT x xT),changeResType_TimeComplexity (snd (fT x xT)))
  end).

Lemma cast_registeredAs_TimeComplexity t1 (tt1 : TT t1) Y (R: registered Y) fT (cast : projT1 (resType tt1) -> Y) (f:t1)
      (Hc : injective cast) :
  projT2 (resType tt1) = registerAs cast Hc ->
  computableTime (ty:=projT2 (changeResType tt1 (TyB Y))) (insertCast R cast f) (changeResType_TimeComplexity fT)->
  computableTime f fT.
Proof.
  intros H [s ints].
  eexists s.
  induction tt1 in cast,f,fT,H,s,ints,Hc |- *.
  -cbn in H,ints|-*;unfold enc in *. rewrite H. exact ints.
  -destruct ints as (?&ints). split. assumption.
   intros x s__x int__x T__x.
   specialize (ints x s__x int__x T__x) as (v &?&ints).
   exists v. split. tauto.
   eapply IHtt1_2. all:eassumption.
Qed.
    
Definition cnst {X} (x:X):nat. exact 0. Qed.
 
Definition callTime2 X Y
           (fT : X -> unit -> nat * (Y -> unit -> nat * unit)) x y : nat :=
  let '(k,f):= fT x tt in k + fst (f y tt).
Arguments callTime2 / {_ _}.


Fixpoint timeComplexity_leq (t : Type) (tt : TT t) {struct tt} : timeComplexity t -> timeComplexity t -> Prop :=
  match tt in (TT t) return timeComplexity t -> timeComplexity t -> Prop with
  | ! t0 => fun _ _ => True
  | @TyArr t1 t2 _ tt2 =>
    fun f f' : timeComplexity (_ -> _) => forall (x:t1) xT, (fst (f x xT)) <= (fst (f' x xT)) /\ timeComplexity_leq (snd (f x xT)) (snd (f' x xT))
  end.

Lemma computesTime_timeLeq X (tt : TT X) x s fT fT':
  timeComplexity_leq fT fT' -> computesTime tt x s fT -> computesTime tt x s fT'.
Proof.
  induction tt in x,s,fT,fT' |-*;intros eq.
  -inv eq. tauto.
  -cbn in eq|-*. intros [H1 H2]. split. 1:tauto.
   intros y t yT ints.
   specialize (H2 y t yT ints ) as (v&R&H2).
   exists v. specialize (eq y yT) as (Hleq&?). split.
   +rewrite <- Hleq. eassumption.
   +eauto.
Qed.
