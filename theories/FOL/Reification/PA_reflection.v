Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Require Import Undecidability.FOL.Reification.GeneralReflection.
Import Vector.VectorNotations.
Require Import String List.

(* ** Signature for PA axiomatisation, containing function symbols for set operations *)

Existing Instance falsity_on.


Inductive PA_funcs : Type :=
  Zero : PA_funcs
| Succ : PA_funcs
| Plus : PA_funcs
| Mult : PA_funcs.

Definition PA_funcs_ar (f : PA_funcs ) :=
match f with
 | Zero => 0
 | Succ => 1
 | Plus => 2
 | Mult => 2
 end.

Inductive PA_preds : Type :=
  Eq : PA_preds.

Definition PA_preds_ar (P : PA_preds) :=
match P with
 | Eq => 2
end.


Instance PA_funcs_signature : funcs_signature :=
{| syms := PA_funcs ; ar_syms := PA_funcs_ar |}.

Instance PA_preds_signature : preds_signature :=
{| preds := PA_preds ; ar_preds := PA_preds_ar |}.




Declare Scope PA_Notation.
Open Scope PA_Notation.

Notation "'zero'" := (@func _ Zero ([])) (at level 1) : PA_Notation.
Notation "'σ' x" := (@func _ Succ ([x])) (at level 37) : PA_Notation.
Notation "x '⊕' y" := (@func _ Plus ([x ; y]) ) (at level 39) : PA_Notation.
Notation "x '⊗' y" := (@func _ Mult ([x ; y]) ) (at level 38) : PA_Notation.
Notation "x '==' y" := (@atom _ _ _ _ Eq ([x ; y])) (at level 40) : PA_Notation.
Notation "x '⧀' y"  := (∃ (x[↑] ⊕ σ $0) == y) (at level 42) : PA_Notation.

Fixpoint num n := match n with 0 => zero | S n => σ (num n) end.

(* ** Axioms of PA *)


Definition ax_zero_succ := ∀  (zero == σ var 0 ~> falsity).
Definition ax_succ_inj :=  ∀∀ (σ $1 == σ $0 ~> $1 == $0).
Definition ax_add_zero :=  ∀  (zero ⊕ $0 == $0).
Definition ax_add_rec :=   ∀∀ ((σ $0) ⊕ $1 == σ ($0 ⊕ $1)).
Definition ax_mult_zero := ∀  (zero ⊗ $0 == zero).
Definition ax_mult_rec :=  ∀∀ (σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0).

Definition ax_induction (phi : form) :=
  phi[zero..] ~> (∀ phi ~> phi[σ $0 .: S >> var]) ~> ∀ phi.



(* Fragment only containing the defining equations for addition and multiplication. *)
Definition FA := ax_add_zero :: ax_add_rec :: ax_mult_zero :: ax_mult_rec :: nil.

(* Full axiomatisation of the theory of PA *)
Inductive PA : form -> Prop :=
  PA_FA phi : In phi FA -> PA phi
| PA_discr : PA ax_zero_succ
| PA_inj : PA ax_succ_inj
| PA_induction phi : PA (ax_induction phi).



(* Equality axioms for the PA signature *)

Definition ax_refl :=  ∀   $0 == $0.
Definition ax_sym :=   ∀∀  $1 == $0 ~> $0 == $1.
Definition ax_trans := ∀∀∀ $2 == $1 ~> $1 == $0 ~> $2 == $0.

Definition ax_succ_congr := ∀∀ $0 == $1 ~> σ $0 == σ $1.
Definition ax_add_congr := ∀∀∀∀ $0 == $1 ~> $2 == $3 ~> $0 ⊕ $2 == $1 ⊕ $3.
Definition ax_mult_congr := ∀∀∀∀ $0 == $1 ~> $2 == $3 ~> $0 ⊗ $2 == $1 ⊗ $3.


Definition EQ :=
  ax_refl :: ax_sym :: ax_trans :: ax_succ_congr :: ax_add_congr :: ax_mult_congr :: nil.

Definition FAeq :=
  EQ ++ FA.

Inductive PAeq : form -> Prop :=
  PAeq_FA phi : In phi FAeq -> PAeq phi
| PAeq_discr : PAeq ax_zero_succ
| PAeq_inj : PAeq ax_succ_inj
| PAeq_induction phi : PAeq (ax_induction phi).

Notation extensional M :=
  (forall x y, @i_atom _ _ _ M Eq ([x ; y]) <-> x = y).


Section ReificationExample.
  Context (D':Type).
  Context {I : interp D'}.
  Context {D_ext : extensional I}.

  Notation "'izero'" := (@i_func _ _ D' I Zero ([])) (at level 1) : PA_Notation.
  Notation "'iσ' x" := (@i_func _ _ D' I Succ ([x])) (at level 37) : PA_Notation.
  Notation "x 'i⊕' y" := (@i_func _ _ D' I Plus ([x ; y]) ) (at level 39) : PA_Notation.
  Notation "x 'i⊗' y" := (@i_func _ _ D' I Mult ([x ; y]) ) (at level 38) : PA_Notation.

  Fixpoint inum n := match n with 0 => izero | S n => iσ (inum n) end.


  Open Scope string_scope.
  Instance PA_reflector : tarski_reflector := buildDefaultTarski 
                        (i_func (f:=Zero) (Vector.nil D')) 
                        (fun k => match k with (Ast.tVar "D'") => true | _ => false end).

  Section ReflectionExtension.
    Import MetaCoq.Template.Ast MetaCoq.Template.TemplateMonad.Core.
    Definition mergeNum (rho:nat -> D) (n:nat) : representsF (inum n) (num n) rho.
    Proof. unfold representsF. induction n.
    * easy.
    * cbn. do 2 f_equal. cbn in IHn. now rewrite IHn.
    Defined.
    MetaCoq Quote Definition qNum := inum.
    MetaCoq Quote Definition qMergeNum := mergeNum.
    MetaCoq Quote Definition qMergeTermNum := @num.

    Definition mergeEqProp (rho:nat -> D) (d1 d2 : D) (t1 t2 : Syntax.term) : representsF d1 t1 rho -> representsF d2 t2 rho -> @representsP _ _ 0 (t1==t2) rho (d1 = d2).
    Proof. intros pt1 pt2. cbn. unfold representsF in pt1, pt2. cbn in pt1, pt2. rewrite pt1, pt2. now rewrite D_ext.
    Defined.
    Definition mEq := (constructForm Eq).
    MetaCoq Quote Definition qMergeFormEq := @mEq.
    MetaCoq Quote Definition qMergeEqProp := mergeEqProp.
    Definition reifyCoqEq : baseConnectiveReifier := fun tct qff l fuel envTerm env fPR fTR => match l with (tv::x::y::nil) => if maybeD tct tv then
                                               xr <- fTR tct qff x envTerm env ;;
                                               yr <- fTR tct qff y envTerm env ;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                               ret (tApp qMergeFormEq (xt::yt::nil), tApp qMergeEqProp (envTerm::x::y::xt::yt::xp::yp::nil)) else fail "Eq applied to wrong type" | _ => fail "Eq constructor applied to != 2 terms" end.
    Definition varsCoqEq : baseConnectiveVars := fun lst fuel tct _ fUVT => match lst with tv::x::y::nil => if maybeD tct tv then
                                               xr <- fUVT x;;
                                               yr <- fUVT y;;
                                               ret (List.app xr yr) else fail "Eq applied to wrong type" | _ => fail "Eq constructor applied to != 2 terms" end.
    Definition reifyBLC (s:string) : baseConnectiveReifier := match s with "eq" => reifyCoqEq | _ => fun _ _ _ _ _ _ _ _ => fail ("Unknown connective " ++ s) end.
    Definition varsBLC (s:string) : baseConnectiveVars := match s with "eq" => varsCoqEq | _ => fun _ _ _ _ _ => fail ("Unknown connective " ++ s) end.
    Definition findVarsTerm : termFinderVars := fun fuel t fUVT => match t with (tApp qMu (k::nil)) => ret nil | _ => fail "Fail" end.
    Definition reifyTerm : termFinderReifier := fun tct qff fuel t envTerm env fTR => match t with tApp qMu (k::nil) => ret (tApp qMergeTermNum (k::nil), tApp qMergeNum (envTerm::k::nil)) | _ => fail "Fail" end.
  End ReflectionExtension.
  Instance PA_reflector_ext : tarski_reflector_extensions PA_reflector := {| (*Cannot define instance in section because they are dropped afterwards *)
    baseLogicConnHelper := Some (reifyBLC);
    baseLogicVarHelper := Some (varsBLC);
    termReifierVarHelper := Some (findVarsTerm);
    termReifierReifyHelper := Some (reifyTerm);
    formReifierVarHelper := None;
    formReifierReifyHelper := None
  |}.

  Definition proj1 {X:Type} {Y:X->Type} (H:{x:X&Y x}) : X := match H with existT x y => x end.

  Lemma foo (a : D) (n:nat) : representableP 1 (fun (b:D) => forall (c:D), exists (d:D), a i⊕ b i⊗ c = iσ d \/ (True /\ False) <-> (inum n = inum n)).
  Proof. represent. Defined.

  Lemma bar : representableP 0 (~(True <-> False)).
  Proof. represent. Defined.

  Compute (fun d n => proj1 (foo d n)).

End ReificationExample.
