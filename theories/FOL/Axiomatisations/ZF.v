(** * Definition of ZF-Entailment *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.


(** ** Signature *)

Existing Instance falsity_on.

Inductive ZF_Funcs : Type :=
| eset : ZF_Funcs
| pair : ZF_Funcs
| union : ZF_Funcs
| power : ZF_Funcs
| om : ZF_Funcs.

Definition ZF_fun_ar (f : ZF_Funcs) : nat :=
  match f with
  | eset => 0
  | pair => 2
  | union => 1
  | power => 1
  | om => 0
  end.

Inductive ZF_Preds : Type :=
| elem : ZF_Preds
| equal : ZF_Preds.

Definition ZF_pred_ar (P : ZF_Preds) : nat :=
  match P with _ => 2 end.

Instance ZF_func_sig : funcs_signature :=
  {| syms := ZF_Funcs; ar_syms := ZF_fun_ar; |}.

Instance ZF_pred_sig : preds_signature :=
  {| preds := ZF_Preds; ar_preds := ZF_pred_ar; |}.

Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.
Notation "¬ A" := (A --> ⊥) (at level 42).
Notation "A '<-->' B" := ((A --> B) ∧ (B --> A)) (at level 43).

(** ** Axioms *)

Notation "x ∈ y" := (atom ZF_func_sig ZF_pred_sig elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 35).
Notation "x ≡ y" := (atom ZF_func_sig ZF_pred_sig equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 35).

Notation "∅" := (func ZF_func_sig eset Vector.nil).
Notation "'ω'" := (func ZF_func_sig om Vector.nil).
Notation "{ x ; y }" := (func ZF_func_sig pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 31).
Notation "⋃ x" := (func ZF_func_sig union (Vector.cons x Vector.nil)) (at level 32).
Notation "'PP' x" := (func ZF_func_sig power (Vector.cons x Vector.nil)) (at level 31).

Notation "x ∪ y" := (⋃ {x; y}) (at level 32).
Notation  "'σ' x" := (x ∪ {x; x}) (at level 32).

Fixpoint shift n x :=
  match n with 
  | O => x
  | S n => subst_term ↑ (shift n x)
  end.

Definition sub x y :=
  ∀ $0 ∈ x[↑] --> $0 ∈ y[↑].

Notation "x ⊆ y" := (sub x y) (at level 34).

Definition ax_ext :=
  ∀ ∀ $1 ⊆ $0 --> $0 ⊆ $1 --> $1 ≡ $0.

Definition ax_eset :=
  ∀ ¬ ($0 ∈ ∅).

Definition ax_pair :=
  ∀ ∀ ∀ $0 ∈ {$1; $2} <--> $0 ≡ $1 ∨ $0 ≡ $2.

Definition ax_union :=
  ∀ ∀ $0 ∈ ⋃ $1 <--> ∃ $0 ∈ $2 ∧ $1 ∈ $0.

Definition ax_power :=
  ∀ ∀ $0 ∈ PP $1 <--> $0 ⊆ $1.

Definition inductive x :=
  ∅ ∈ x ∧ ∀ $0 ∈ shift 1 x --> σ $0 ∈ shift 1 x.

Definition ax_om1 :=
  inductive ω.

Definition ax_om2 :=
  ∀ inductive $0 --> ω ⊆ $0.

Definition ax_sep phi :=
  ∀ ∃ ∀ $0 ∈ $1 <--> $0 ∈ $2 ∧ phi[$0.: Nat.add 3 >> var].

Definition fun_rel phi :=
  ∀ ∀ ∀ phi[$2 .: ($1 .: (Nat.add 3 >> var))] --> phi[$2 .: ($0 .: (Nat.add 3 >> var))] --> $1 ≡ $0.

Definition ax_rep phi :=
  fun_rel phi --> ∀ ∃ ∀ $0 ∈ $1 <--> ∃ $0 ∈ $3 ∧ phi[$0 .: ($1 .: (Nat.add 4 >> var))].



(** ** ZF-Models *)

Class ZF_Model :=
  {
    V :> Type ;
    VI : interp V ;
    
    V_ext : forall rho, rho ⊨ ax_ext ;
    V_eset : forall rho, rho ⊨ ax_eset ;
    V_pair : forall rho, rho ⊨ ax_pair ;
    V_union : forall rho, rho ⊨ ax_union ;
    V_power : forall rho, rho ⊨ ax_power ;
    V_om1 : forall rho, rho ⊨ ax_om1 ;
    V_om2 : forall rho, rho ⊨ ax_om2 ;
    V_sep : forall phi rho, rho ⊨ ax_sep phi ;
    V_rep : forall phi rho, rho ⊨ ax_rep phi ;
  }.

Coercion V : ZF_Model >-> Sortclass.
Instance VI_instance (M : ZF_Model) : interp M := @VI M.

Notation "x i∈ y" := (@i_atom _ _ _ VI elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x i≡ y" := (@i_atom _ _ _ VI equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x i⊆ y" := (forall z, z i∈ x -> z i∈ y) (at level 20).

Notation "i∅" := (@i_func _ _ _ VI eset Vector.nil).
Notation "'iω'" := (@i_func _ _ _ VI om Vector.nil).
Notation "i{ x ; y }" := (@i_func _ _ _ VI pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 10).
Notation "i⋃ x" := (@i_func _ _ _ VI union (Vector.cons x Vector.nil)) (at level 15).
Notation "'iPP' x" := (@i_func _ _ _ VI power (Vector.cons x Vector.nil)) (at level 15).

Notation "x i∪ y" := (i⋃ i{x; y}) (at level 16).
Notation "'iσ' x" := (x i∪ i{x; x}) (at level 15).

(* Extensional models interpret set equality as equality *)

Notation extensional M :=
  (forall x y : M, x i≡ y <-> x = y).

(* Standard models contain only standard natural numbers *)

Fixpoint numeral {M : ZF_Model} n :=
  match n with 
  | O => i∅
  | S n => iσ (numeral n)
  end.

Definition standard (M : ZF_Model) :=
  forall x, x i∈ iω -> exists n, x = numeral n.



(** ** ZF-Entailment *)

Definition ZF_entails phi :=
  forall (M : ZF_Model), extensional M -> forall rho, rho ⊨ phi.



(** ** Internal axioms *)

Section ZF.

  Context { M : ZF_Model }.

  Hypothesis VIEQ : extensional M.
  
  Lemma M_ext (x y : M) :
    x i⊆ y -> y i⊆ x -> x = y.
  Proof.
    rewrite <- VIEQ. apply (V_ext (fun _ => i∅)).
  Qed.

  Lemma M_eset x :
    ~ x i∈ i∅.
  Proof.
    specialize V_eset with (rho:=fun _ => i∅). cbn.
    intros H1 H2. now apply (H1 x).
  Qed.

  Lemma M_pair x y z :
    x i∈ i{y; z} <-> x = y \/ x = z.
  Proof.
    rewrite <- !VIEQ. apply V_pair with (rho:=fun _ => i∅).
  Qed.

  Lemma M_union x y :
    x i∈ i⋃ y <-> exists z, z i∈ y /\ x i∈ z.
  Proof.
    apply V_union with (rho:=fun _ => i∅).
  Qed.

  Lemma M_power x y :
    x i∈ iPP y <-> x i⊆ y.
  Proof.
    apply V_power with (rho:=fun _ => i∅).
  Qed.

  Definition M_inductive x :=
    i∅ i∈ x /\ forall y, y i∈ x -> iσ y i∈ x.

  Lemma M_om1 :
    M_inductive iω.
  Proof.
    apply V_om1 with (rho:=fun _ => i∅).
  Qed.

  Lemma M_om2 x :
    M_inductive x -> iω i⊆ x.
  Proof.
    apply V_om2 with (rho:=fun _ => i∅).
  Qed.

  Definition agrees_fun phi (P : M -> Prop) :=
    forall x rho, P x <-> (x.:rho) ⊨ phi.

  Definition representable (P : V -> Prop) :=
    exists phi rho, forall d, P d <-> (d.:rho) ⊨ phi.

  Lemma M_sep P x :
    representable P -> exists y, forall z, z i∈ y <-> z i∈ x /\ P z.
  Proof.
    intros [phi [rho Hp]]. specialize V_sep with (rho:=rho). cbn.
    intros H. destruct (H phi x) as [y H']. clear H.
    exists y. intros z. specialize (H' z). setoid_rewrite sat_comp in H'.
    rewrite (sat_ext _ _ (xi:=z.:rho)) in H'; try now intros [].
    firstorder.
  Qed.

  Definition functional (R : M -> M -> Prop) :=
    forall x y y', R x y -> R x y' -> y = y'.

  Definition def_rel (R : M -> M -> Prop) :=
    exists phi rho, forall x y, R x y <-> (x.:(y.:rho)) ⊨ phi.

  Definition M_is_rep R x y :=
    forall v, v i∈ y <-> exists u, u i∈ x /\ R u v.

  Lemma M_rep R x :
    def_rel R -> functional R -> exists y, M_is_rep R x y.
  Proof.
    intros [phi [rho Hp]]. specialize V_rep with (rho:=rho). intros H1 H2.
    cbn in H1. specialize (H1 phi). destruct H1 with x as [y Hy].
    - intros a b b'. setoid_rewrite sat_comp.
      erewrite sat_ext. rewrite <- (Hp a b). 2: now intros [|[]].
      erewrite sat_ext. rewrite <- (Hp a b'). 2: now intros [|[]].
      rewrite VIEQ. apply H2.
    - exists y. intros v. split.
      + intros [u[U1 U2]] % Hy. exists u. split; trivial.
        setoid_rewrite sat_comp in U2. rewrite sat_ext in U2. rewrite (Hp u v). apply U2. now intros [|[]]; cbn.
      + intros [u[U1 U2]]. apply Hy. exists u. split; trivial.
        setoid_rewrite sat_comp. rewrite sat_ext. rewrite <- (Hp u v). apply U2. now intros [|[]]; cbn.
  Qed.

  Lemma is_rep_unique R x y y' :
    M_is_rep R x y -> M_is_rep R x y' -> y = y'.
  Proof.
    intros H1 H2. apply M_ext; intros v.
    - intros H % H1. now apply H2.
    - intros H % H2. now apply H1.
  Qed.


End ZF.
