(** * Definition of ZF-Entailment *)

From Undecidability.FOLP Require Export FullTarski.



(** ** Signature *)

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

Instance ZF_Signature : Signature :=
  {| Funcs := ZF_Funcs; fun_ar := ZF_fun_ar; Preds := ZF_Preds; pred_ar := ZF_pred_ar |}.



(** ** Axioms *)

Notation "x ∈ y" := (Pred elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x ≡ y" := (Pred equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "$ x" := (var_term x) (at level 1).

Notation "∅" := (Func eset Vector.nil).
Notation "'ω'" := (Func om Vector.nil).
Notation "{ x ; y }" := (Func pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 10).
Notation "⋃ x" := (Func union (Vector.cons x Vector.nil)) (at level 15).
Notation "'PP' x" := (Func power (Vector.cons x Vector.nil)) (at level 15).

Notation "x ∪ y" := (⋃ {x; y}) (at level 16).
Notation "'σ' x" := (x ∪ {x; x}) (at level 15).

Fixpoint shift n x :=
  match n with 
  | O => x
  | S n => subst_term ↑ (shift n x)
  end.

Definition sub x y :=
  ∀ $0 ∈ shift 1 x --> $0 ∈ shift 1 y.

Notation "x ⊆ y" := (sub x y) (at level 20).

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
  ∀ ∃ ∀ $0 ∈ $1 <--> $0 ∈ $2 ∧ phi.

Definition fun_rel phi :=
  ∀ ∀ ∀ phi[$2.:$1..] --> phi[$2.:$0..] --> $1 ≡ $0.

Definition ax_rep phi :=
  fun_rel phi --> ∀ ∃ ∀ $0 ∈ $1 <--> ∃ $0 ∈ $3 ∧ phi.



(** ** Bounded Formulas *)

Inductive bounded_term (n : nat) : term -> Prop :=
| clt_var m : m < n -> bounded_term n (var_term m)
| clt_Func F v : (forall t, vec_in t v -> bounded_term n t) -> bounded_term n (Func F v).

Inductive bounded (n : nat) : form -> Prop :=
| cl_Fal : bounded n Fal
| cl_Pred P v : (forall t, vec_in t v -> bounded_term n t) -> bounded n (Pred P v)
| cl_Impl phi psi : bounded n phi -> bounded n psi -> bounded n (Impl phi psi)
| cl_Conj phi psi : bounded n phi -> bounded n psi -> bounded n (Conj phi psi)
| cl_Disj phi psi : bounded n phi -> bounded n psi -> bounded n (Disj phi psi)
| cl_Ex phi : bounded (S n) phi -> bounded n (Ex phi)
| cl_All phi : bounded (S n) phi -> bounded n (All phi).

Lemma eval_bounded D {I : interp D} t n rho rho' :
  bounded_term n t -> (forall k, k < n -> rho k = rho' k) -> eval rho t = eval rho' t.
Proof.
  induction 1; cbn; intros HB; auto.
  f_equal. apply vec_map_ext. auto.
Qed.

Lemma bound_step D {I : interp D} n (rho rho' : nat -> D) d :
  (forall k, k < n -> rho k = rho' k) -> forall k, k < S n -> (d .: rho) k = (d .: rho') k.
Proof.
  intros H k Hk. destruct k; cbn; trivial. apply H. lia.
Qed.

Lemma sat_bounded D {I : interp D} phi n rho rho' :
  bounded n phi -> (forall k, k < n -> rho k = rho' k) -> rho ⊨ phi <-> rho' ⊨ phi.
Proof.
  induction 1 in rho, rho' |-*; cbn; intros HB.
  - tauto.
  - now rewrite (vec_map_ext (fun x h => eval_bounded (H x h) HB)).
  - rewrite IHbounded1, IHbounded2; eauto. tauto.
  - rewrite IHbounded1, IHbounded2; eauto. tauto.
  - rewrite IHbounded1, IHbounded2; eauto. tauto.
  - split; intros [d H']; exists d; eapply (IHbounded (d .: rho) (d .: rho')), H'.
    all: now apply bound_step.
  - split; intros H' d; eapply (IHbounded (d .: rho) (d .: rho') _), H'.
    Unshelve. all: now apply bound_step.
Qed.

Lemma sat_bounded0 D {I : interp D} phi rho rho' :
  bounded 0 phi -> rho ⊨ phi -> rho' ⊨ phi.
Proof.
  intros H1 H2. apply (sat_bounded H1 (rho':=rho)); trivial.
  intros k Hk. exfalso. lia.
Qed.

Lemma sat_bounded1 D {I : interp D} phi x rho rho' :
  bounded 1 phi -> (x.:rho) ⊨ phi -> (x.:rho') ⊨ phi.
Proof.
  intros H1 H2. apply (sat_bounded H1 (rho':=x.:rho)); trivial.
  intros k Hk. assert (k = 0) as -> by lia. reflexivity.
Qed.

Lemma sat_bounded2 D {I : interp D} phi x y rho rho' :
  bounded 2 phi -> (x.:(y.:rho)) ⊨ phi -> (x.:(y.:rho')) ⊨ phi.
Proof.
  intros H1 H2. apply (sat_bounded H1 (rho':=x.:(y.:rho))); trivial.
  intros k Hk. assert (k = 0 \/ k = 1) as [->| ->] by lia; reflexivity.
Qed.



(** ** ZF-Models *)

Class ZF_Model :=
  {
    V :> Type ;
    VI : @interp ZF_Signature V ;
    
    V_ext : forall rho, rho ⊨ ax_ext ;
    V_eset : forall rho, rho ⊨ ax_eset ;
    V_pair : forall rho, rho ⊨ ax_pair ;
    V_union : forall rho, rho ⊨ ax_union ;
    V_power : forall rho, rho ⊨ ax_power ;
    V_om1 : forall rho, rho ⊨ ax_om1 ;
    V_om2 : forall rho, rho ⊨ ax_om2 ;
    V_sep : forall phi rho, bounded 1 phi -> rho ⊨ ax_sep phi ;
    V_rep : forall phi rho, bounded 2 phi -> rho ⊨ ax_rep phi ;
  }.

Coercion V : ZF_Model >-> Sortclass.
Instance VI_instance (M : ZF_Model) : @interp ZF_Signature M := @VI M.

Notation "x ∈ y" := (@i_P _ _ VI elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x ≡ y" := (@i_P _ _ VI equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "$ x" := (var_term x) (at level 1).
Notation "x ⊆ y" := (forall z, z ∈ x -> z ∈ y) (at level 20).

Notation "∅" := (@i_f _ _ VI eset Vector.nil).
Notation "'ω'" := (@i_f _ _ VI om Vector.nil).
Notation "{ x ; y }" := (@i_f _ _ VI pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 10).
Notation "⋃ x" := (@i_f _ _ VI union (Vector.cons x Vector.nil)) (at level 15).
Notation "'PP' x" := (@i_f _ _ VI power (Vector.cons x Vector.nil)) (at level 15).

Notation "x ∪ y" := (⋃ {x; y}) (at level 16).
Notation "'σ' x" := (x ∪ {x; x}) (at level 15).

(* Extensional models interpret set equality as equality *)

Notation extensional M :=
  (forall x y : M, x ≡ y <-> x = y).

(* Standard models contain only standard natural numbers *)

Fixpoint numeral {M : ZF_Model} n :=
  match n with 
  | O => ∅
  | S n => σ (numeral n)
  end.

Definition standard (M : ZF_Model) :=
  forall x, x ∈ ω -> exists n, x = numeral n.



(** ** ZF-Entailment *)

Definition ZF_entails phi :=
  forall (M : ZF_Model), extensional M -> forall rho, rho ⊨ phi.





