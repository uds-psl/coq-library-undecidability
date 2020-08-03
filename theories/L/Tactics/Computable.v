From Undecidability.L Require Export Util.L_facts Tactics.Extract.
Require Import PslBase.Bijection String.

(** * Correctness and time bounds *)

(* Typeclass for registering types *)


Class registered (X : Type) := mk_registered
  {
    enc :> encodable X ; (* the encoding function for X *)
    proc_enc : forall x, proc (enc x) ; (* encodings need to be a procedure *)
    inj_enc : injective enc (* encoding is injective *)
  }.

Hint Mode registered + : typeclass_instances. (* treat argument as input and force evar-freeness*)

Arguments enc : simpl never.  (* Never unfold with cbn/simpl *)

(** ** Correctness *)

(* Definition of the valid types for extraction *)

Inductive TT : Type -> Type :=
  TyB t (R : registered t) : TT t
| TyArr t1 t2 (tt1 : TT t1) (tt2 : TT t2)
  : TT (t1 -> t2).

Existing Class TT.
Existing Instance TyB.
Existing Instance TyArr.
  
Arguments TyB _ {_}.
Arguments TyArr {_} {_} _ _.

Hint Mode TT + : typeclass_instances. (* treat argument as input and force evar-freeness*)

Notation "! X" := (TyB X) (at level 69).
Notation "X ~> Y" := (TyArr X Y) (right associativity, at level 70).


Fixpoint computes {A} (tau : TT A) {struct tau}: A -> L.term -> Type :=
  match tau with
    !_ => fun x xInt => (xInt = enc x)
  | @TyArr A B tau1 tau2 =>
    fun f t_f  =>
      proc t_f * forall (a : A) t_a,
        computes tau1 a t_a
        ->  {v : term & (app t_f t_a >* v) * computes tau2 (f a) v}
  end%type.

Lemma computesProc t (ty : TT t) (f : t) fInt:
  computes ty f fInt -> proc fInt.
Proof.
  destruct ty.
  -intros ->. unfold enc. now destruct R. 
  -now intros [? _].
Qed.

(* This is for a user to give an definition *)
Class computable X {ty : TT X} (x : X) : Type :=
  {
    ext : extracted x;
    extCorrect : computes ty x ext;
  }.

Global Arguments computable {X} {ty} x.
Global Arguments extCorrect {X} ty x {computable} : simpl never.
Global Arguments ext {X} {ty} x {computable} : simpl never.

Hint Mode computable + - +: typeclass_instances. (* treat argument as input and force evar-freeness*)
Hint Extern 4 (@extracted ?t ?f) => let ty := constr:(_ : TT t) in notypeclasses refine (ext (ty:=ty) f) : typeclass_instances.

Typeclasses Opaque ext.

Lemma proc_ext X (ty : TT X) (x : X) ( H : computable x) : proc (ext x).
Proof.
  unfold ext. destruct H. apply (computesProc extCorrect0). 
Qed.


Instance reg_is_ext ty (R : registered ty) (x : ty) : computable x.
Proof.
  exists (enc x). reflexivity.
Defined.


Lemma computesTyB (t:Type) (x:t) `{registered t}: computes (TyB t) x (ext x).
Proof.
  unfold ext. now destruct R.
Qed.

Instance extApp' t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) (Hf : computable f) (Hx : computable x) : computable (f x).
Proof.
  destruct Hf, Hx.
  edestruct extCorrect0 as [? H].
  edestruct H as (?&?&?).
  eassumption.
  now eapply (@Build_computable _ _ _ x0). 
Defined.  

Lemma extApp t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) (Hf : computable f) (Hx : computable x) :
  app (ext f) (ext x) >* ext (f x).
Proof.
  unfold ext, extApp'.
  destruct Hf, Hx.
  destruct extCorrect0 as (? & correct0).
  destruct correct0 as (?&?&?). tauto. 
Qed.

Lemma ext_is_enc t1 (R:registered t1) (x: t1) (Hf : computable x) :
  @ext _ _ x Hf = enc x.
Proof.
  now destruct Hf. 
Defined.

Definition computesExp {t} (ty : TT t) (f:t) (s fExt : term) : Type :=
  eval s fExt * computes ty f fExt.

Lemma computesExpStart t1 (tt1 : TT t1) (f : t1) (fExt : term):
  proc fExt ->
  {v :term & computesExp tt1 f fExt v} ->  computes tt1 f fExt.
Proof.
  intros ? (?&?&?). replace fExt with x. tauto. apply unique_normal_forms. eapply e. eapply H. destruct e as [e ?]. now rewrite e. 
Qed.

Lemma computesExpStep t1 t2 (tt1 : TT t1) (tt2 : TT t2) (f : t1 -> t2) (s:term) (fExt : term):
  eval s fExt -> closed s -> 
  (forall (y : t1) (yExt : term), computes tt1 y yExt -> {v : term & computesExp tt2 (f y) (app s yExt) v}%type) ->
  computesExp (tt1 ~> tt2) f s fExt.
Proof.
  intros ? ? H. split. assumption. split. split. now rewrite <-H0. now destruct H0.
  intros ? ? exted.
  edestruct H as (v&?&?). eassumption. 
  eexists v. split. rewrite H0 in e. now rewrite e. eauto.
Qed.

Lemma computesTyArr t1 t2 (tt1 : TT t1) (tt2 : TT t2) f fExt :
  proc fExt
  -> (forall (y : t1) (yExt : term),
        computes tt1 y yExt
        -> {v : term & eval (app fExt yExt) v * (proc v -> computes tt2 (f y) v)}%type)
  -> computes (tt1 ~> tt2) f fExt.
Proof.
  intros ? H'.
  split;[assumption|].
  intros y yExt yCorrect.
  edestruct H' as (?&(R&?) & H''). eassumption. 
  eexists. split.
  eassumption. 
  eapply H''.
  split. 2:assumption.
  rewrite <- R. apply app_closed. now destruct H. specialize (computesProc yCorrect) as []. easy.
Qed.

(** Extensional equality to extract similar functions without unsopported features (e.g. informative deciders) instead *)

Fixpoint extEq t {tt:TT t} : t -> t -> Prop:=
  match tt with
    TyB _ _ => eq
  | @TyArr t1 t2 tt1 tt2 => fun f f' => forall (x : t1), extEq (f x) (f' x)
  end.


Instance extEq_refl t (tt:TT t): Reflexive (extEq (tt:=tt)).
Proof.
  unfold Reflexive.
  induction tt;cbn.
  -reflexivity.
  -intros f x. eauto.
Qed.

Lemma computesExt X (tt : TT X) (x x' : X) s:
  extEq x x' -> computes tt x s -> computes tt x' s.
Proof.
  induction tt in x,x',s |-*;intros eq.
  -inv eq. tauto.
  -cbn in eq|-*. intros [H1 H2]. split. 1:tauto.
   intros y t exts.
   specialize (H2 y t exts) as (v&R&H2).
   exists v. split. 1:assumption.
   eapply IHtt2. 2:now eassumption.
   apply eq.
Qed.

Lemma computableExt X (tt : TT X) (x x' : X):
  extEq x x' -> computable x -> computable x'.
  intros ? (s&?). exists s. eauto using computesExt.
Defined.

(** register a datatype via an (injectve) function to another, e.g. vectors as lists *)

Lemma registerAs X Y `{registered X} (f:Y -> X) : injective f -> registered Y.
Proof.
  intros Hf. eexists (fun x => enc (f x)). now destruct H.
  intros ? ? ?. now eapply H, Hf in H0.
Defined.
Arguments registerAs {_ _ _} _ _.

(** Support for extracting registerAs-ed functions *)

Fixpoint changeResType t1 t2 (tt1:TT t1) (tt2 : TT t2) : {t & TT t}:=
  match tt1 with
    TyB _ _ => existT _ t2 tt2
  | TyArr _ _ tt11 tt12 =>
    existT _ _ (TyArr tt11 (projT2 (changeResType tt12 tt2)))
  end.

Fixpoint resType t1 (tt1 : TT t1) : {t & registered t} :=
  match tt1 with
    @TyB _ R => existT _ _ R
  | TyArr _ _ _ t2 => resType t2
  end.

Fixpoint insertCast t1 (tt1 : TT t1) Y (R: registered Y) {struct tt1}:
  forall (cast : projT1 (resType tt1) -> Y) (f : t1), projT1 (changeResType tt1 (TyB Y)) :=
  match tt1 with
    TyB _ _ => fun cast x => cast x
  | TyArr _ _ tt11 tt12 => fun cast f x=> (insertCast (tt1:=tt12) R cast (f x))
  end.


Lemma cast_registeredAs t1 (tt1 : TT t1) Y (R: registered Y) (cast : projT1 (resType tt1) -> Y) (f:t1)
  (Hc : injective cast) :
  projT2 (resType tt1) = registerAs cast Hc ->
  computable (ty:=projT2 (changeResType tt1 (TyB Y))) (insertCast R cast f) ->
  computable f.
Proof.
  intros H (s&exts).
  exists s.
  induction tt1 in cast,f,H,s,exts,Hc |- *.
  -cbn in H,exts|-*;unfold enc in *. rewrite H. exact exts.
  -destruct exts as (?&exts). split. assumption.
   intros x s__x ext__x.
   specialize (exts x s__x ext__x) as (v &?&exts).
   exists v. split. tauto.
   eapply IHtt1_2. all:eassumption.
Qed.

Opaque computes.
