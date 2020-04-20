Require Import Vector.

(** * Proposed new definition of First Order Logic in Coq *)

(**

Renaming table w.r.t. the three existing developments

new name     | TRAKH name     | completeness name
--------------------------------------------------
syms         | syms           | Funcs
ar_syms      | ar_syms        | fun_ar
var          | in_var         | var_term
func         | in_fot         | Func
preds        | rels           | Preds
ar_preds     | ar_rels        | pred_ar
binop        | fol_bop        | -
quantop      | fol_qop        | -
fal          | fol_false      | Fal
atom         | fol_atom       | Pred
bin          | fol_bin        | Impl / ...
quant        | fol_quant      | All / ...

*)

(** Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
          |0 => x
          |S n => xi n
          end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

(** Signatures are a record to allow for easier definitions of general transformations on signatures *)
Record signature :=
  Mk_signature {
      symbols : Type ;
      arity : symbols -> nat;
    }.

(** Make two aliases of signatures type classes so they can become proper implicits *)
Definition funcs_signature := signature.
Existing Class funcs_signature.

Definition preds_signature := signature.
Existing Class preds_signature.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  Notation syms := (symbols Σ_funcs).
  Notation ar_syms := (arity Σ_funcs).

  (** We use the stdlib definition of vectors to be maximally compatible  *)
  Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), Vector.t term (ar_syms f) -> term.

  Fixpoint subst_term   (σ : nat -> term) (t : term) : term :=
    match t with
    | var t => σ t
    | func f v => func f (Vector.map (subst_term σ) v)
    end.

  Context {Σ_preds : preds_signature}.

  Notation preds := (symbols Σ_preds).
  Notation ar_preds := (arity Σ_preds).

  (** Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.

  (** Formulas have falsity as fixed constant -- we could parametrise against this in principle *)
  Inductive form  : Type :=
  | fal : form
  | atom : forall (P : preds), Vector.t term (ar_preds P) -> form
  | bin : binop -> form  -> form  -> form
  | quant : quantop -> form  -> form.

  Definition up (σ : nat -> term) := scons (var 0) (funcomp (subst_term (funcomp var S)) σ).

  Fixpoint subst_form (σ : nat -> term) (phi : form) : form :=
    match phi with
    | fal => fal
    | atom P v => atom P (Vector.map (subst_term σ) v)
    | bin op phi1 phi2 => bin op (subst_form σ phi1) (subst_form σ phi2)
    | quant op phi => quant op (subst_form (up σ) phi)
    end.

End fix_signature.

(** Setting implicit arguments is crucial  *)
(** We can write term both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Compute (term _).
Compute term.

Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Compute (var 0).
Compute (var _ 0).
Compute (func _ _).

Arguments subst_term {_} _ _.

(** Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
Arguments form  _ _ _, _ _ {_}, {_ _ _}.
Arguments fal   _ _ _, _ _ {_}, {_ _ _}.
Arguments atom  _ _ _, _ _ {_}, {_ _ _}.
Arguments bin   _ _ _, _ _ {_}, {_ _ _}.
Arguments quant _ _ _, _ _ {_}, {_ _ _}.

Arguments up         _, {_}.
Arguments subst_form _ _ _, _ _ {_}, {_ _ _}.
