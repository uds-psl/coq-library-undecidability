(** * ZF Set Theory *)

From Undecidability.FOLP Require Export FullTarski.
From Undecidability.Problems Require Export PCP.



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



(** ** Axioms *)

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

(* Definition ax_refl :=
  ∀ $0 ≡ $0.

Definition ax_rewrite phi :=
  ∀ ∀ $0 ≡ $1 --> phi[$0..] --> phi[$1..]. *)



(** ** PCP Reduction *)

Definition sing a :=
  {a; a}.

Definition opair a b :=
  {{a; a}; {a; b}}.

Definition pairing f A :=
  ∀ $0 ∈ shift 1 f --> ∃ ∃ $1 ∈ shift 3 A ∧ $2 ≡ opair $1 $0.

Definition function f A :=
  pairing f A ∧ ∀ ∃ $0 ∈ shift 2 A ∧ opair $0 $1 ∈ shift 2 f
                    ∧ ∀ opair $1 $0 ∈ shift 2f --> $2 ≡ $0.

Definition function' f :=
  ∀ ∀ ∀ opair $2 $1 ∈ shift 3 f --> opair $2 $0 ∈ shift 3 f --> $1 ≡ $0.

Definition enc_bool (x : bool) :=
  if x then {∅; ∅} else ∅.

Fixpoint prep_string (s : string bool) a :=
  match s with
  | nil => a
  | b::s => opair (enc_bool b) (prep_string s a)
  end.

Definition enc_string (s : string bool) :=
  prep_string s ∅.

Fixpoint enc_stack (B : BSRS) :=
  match B with
  | nil => ∅
  | (s,t)::B => enc_stack B ∪ sing (opair (enc_string s) (enc_string t))
  end.

Definition is_rep phi a b :=
  ∀ $0 ∈ shift 1 b <--> ∃ $0 ∈ shift 2 a ∧ phi.

Definition comb_rel s t :=
  ∃ ∃ $2 ≡ opair $0 $1 ∧ $3 ≡ opair (prep_string s $0) (prep_string t $1).

Fixpoint combinations (B : BSRS) a b :=
  match B with
  | nil => b ≡ ∅
  | (s,t)::B => ∃ ∃ shift 2 b ≡ $0 ∪ $1 ∧ combinations B (shift 2 a) $1
                   ∧ is_rep (comb_rel s t) (shift 2 a) $0
  end.

Definition solutions (B : BSRS) f n :=
  opair ∅ (enc_stack B) ∈ f ∧ ∀ ∀ ∀ $2 ∈ shift 3 n --> opair $2 $1 ∈ shift 3 f
               --> combinations B $1 $0 --> opair (σ $2) $0 ∈ shift 3 f.

Definition solvable (B : BSRS) :=
  ∃ ∃ ∃ ∃ ∃ $4 ∈ ω ∧ function' $3 ∧ solutions B $3 $4 ∧ opair $4 $0 ∈ $3 ∧ $2 ∈ $0 ∧ $2 ≡ opair $1 $1.



(** ** Models *)

Notation "phi <--> psi" := ((phi --> psi) ∧ (psi --> phi)) (right associativity, at level 55).

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

Lemma bound_step D (I : interp D) n (rho rho' : nat -> D) d :
  (forall k, k < n -> rho k = rho' k) -> forall k, k < S n -> (d .: rho) k = (d .: rho') k.
Proof.
  intros H k Hk. destruct k; cbn; trivial. apply H. lia.
Qed.

Lemma sat_bounded D (I : interp D) phi n rho rho' :
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

Class ZF_Model :=
  {
    V :> Type ;
    VI : @interp ZF_Signature V ;
    (*VIS : i_F (domain:=V) -> False ;*)
    
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

Section ZF.

  Context { M : ZF_Model }.
  Instance VIM : @interp ZF_Signature V := VI.

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

  Hypothesis VIEQ : forall x y, x ≡ y <-> x = y.
  
  Lemma M_ext (x y : M) :
    x ⊆ y -> y ⊆ x -> x = y.
  Proof.
    rewrite <- VIEQ. apply V_ext with (rho:=fun _ => ∅).
  Qed.

  Lemma M_eset x :
    ~ x ∈ ∅.
  Proof.
    specialize V_eset with (rho:=fun _ => ∅). cbn.
    intros H1 H2. now apply (H1 x).
  Qed.

  Lemma M_pair x y z :
    x ∈ {y; z} <-> x = y \/ x = z.
  Proof.
    rewrite <- !VIEQ. apply V_pair with (rho:=fun _ => ∅).
  Qed.

  Lemma M_union x y :
    x ∈ ⋃ y <-> exists z, z ∈ y /\ x ∈ z.
  Proof.
    apply V_union with (rho:=fun _ => ∅).
  Qed.

  Lemma M_power x y :
    x ∈ PP y <-> x ⊆ y.
  Proof.
    apply V_power with (rho:=fun _ => ∅).
  Qed.

  Definition M_inductive x :=
    ∅ ∈ x /\ forall y, y ∈ x -> σ y ∈ x.

  Lemma M_om1 :
    M_inductive ω.
  Proof.
    apply V_om1 with (rho:=fun _ => ∅).
  Qed.

  Lemma M_om2 x :
    M_inductive x -> ω ⊆ x.
  Proof.
    apply V_om2 with (rho:=fun _ => ∅).
  Qed.

  Lemma sat_bounded0 phi rho rho' :
    bounded 0 phi -> rho ⊨ phi -> rho' ⊨ phi.
  Proof.
    intros H1 H2. apply (sat_bounded VI H1 (rho':=rho)); trivial.
    intros k Hk. exfalso. lia.
  Qed.

  Lemma sat_bounded1 phi x rho rho' :
    bounded 1 phi -> (x.:rho) ⊨ phi -> (x.:rho') ⊨ phi.
  Proof.
    intros H1 H2. apply (sat_bounded VI H1 (rho':=x.:rho)); trivial.
    intros k Hk. assert (k = 0) as -> by lia. reflexivity.
  Qed.

  Lemma sat_bounded2 phi x y rho rho' :
    bounded 2 phi -> (x.:(y.:rho)) ⊨ phi -> (x.:(y.:rho')) ⊨ phi.
  Proof.
    intros H1 H2. apply (sat_bounded VI H1 (rho':=x.:(y.:rho))); trivial.
    intros k Hk. assert (k = 0 \/ k = 1) as [->| ->] by lia; reflexivity.
  Qed.

  Definition agrees_fun phi (P : M -> Prop) :=
    forall x rho, P x <-> (x.:rho) ⊨ phi.

  Definition def_pred P :=
    exists phi, bounded 1 phi /\ agrees_fun phi P.

  Lemma M_sep P x :
    def_pred P -> exists y, forall z, z ∈ y <-> z ∈ x /\ P z.
  Proof.
    intros [phi [H1 H2]]. specialize V_sep with (rho:=fun _ => ∅). cbn.
    intros H. destruct (H phi H1 x) as [y H']. clear H.
    exists y. intros z. specialize (H' z). now rewrite <- (H2 z) in H'.
  Qed.

  Definition functional (R : M -> M -> Prop) :=
    forall x y y', R x y -> R x y' -> y = y'.

  Definition agrees_rel phi (R : M -> M -> Prop) :=
    forall x y rho, R x y <-> (x.:(y.:rho)) ⊨ phi.

  Definition def_rel (R : M -> M -> Prop) :=
    exists phi, bounded 2 phi /\ agrees_rel phi R.

  Lemma functional_fun_rel phi R rho :
    bounded 2 phi -> agrees_rel phi R -> functional R -> rho ⊨ fun_rel phi.
  Proof.
    cbn. intros HP HD HR a b b' HB HB'. apply VIEQ, (HR a b b').
    - apply (HD a b (b'.:rho)). apply (sat_comp VI) in HB.
      asimpl in HB. cbn in HB. eapply sat_bounded2; eauto.
    - apply (HD a b' (b.:rho)). apply (sat_comp VI) in HB'.
      asimpl in HB'. cbn in HB'. eapply sat_bounded2; eauto.
  Qed.

  Definition M_is_rep R x y :=
    forall v, v ∈ y <-> exists u, u ∈ x /\ R u v.

  Lemma M_rep R x :
    def_rel R -> functional R -> exists y, M_is_rep R x y.
  Proof.
    intros [phi [H1 H2]] HR. specialize V_rep with (rho:=fun _ => ∅). cbn.
    intros H. destruct (H phi H1 (functional_fun_rel H1 H2 HR) x) as [y H']; clear H.
    exists y. intros v. specialize (H' v). split.
    - intros [u HU] % H'. rewrite <- (H2 u v) in HU. now exists u.
    - intros [u HU]. apply H'. exists u. now rewrite <- (H2 u v).
  Qed.



  (** Completeness **)

  Fixpoint numeral n :=
    match n with 
    | O => ∅
    | S n => σ (numeral n)
    end.

  Definition append_all A (c : card bool) :=
    map (fun p => (fst c ++ fst p, snd c ++ snd p)) A.

  Definition derivation_step B C :=
    flat_map (append_all C) B.

  Fixpoint derivations B n :=
    match n with
    | O => B
    | S n => derivation_step B (derivations B n)
    end.

  Lemma derivable_derivations B s t :
    derivable B s t -> exists n, s/t el derivations B n.
  Proof.
    induction 1.
    - exists 0. apply H.
    - destruct IHderivable as [n Hn]. exists (S n).
      apply in_flat_map. exists (x, y). split; trivial.
      apply in_map_iff. exists (u,v). cbn. split; trivial.
  Qed.

  Definition M_sing x :=
    {x; x}.

  Definition M_opair x y := ({{x; x}; {x; y}}).

  Definition M_function f :=
    forall x y y', M_opair x y ∈ f -> M_opair x y' ∈ f -> y = y'.

  Definition M_enc_bool (x : bool) :=
    if x then {∅; ∅} else ∅.

  Fixpoint M_prep_string (s : string bool) x :=
    match s with
    | nil => x
    | b::s => M_opair (M_enc_bool b) (M_prep_string s x)
    end.

  Definition M_enc_string (s : string bool) :=
    M_prep_string s ∅.

  Definition M_enc_card s t :=
    M_opair (M_enc_string s) (M_enc_string t).

  Fixpoint M_enc_stack (B : BSRS) :=
    match B with
    | nil => ∅
    | (s,t)::B => M_enc_stack B ∪ M_sing (M_enc_card s t)
    end.

  Lemma eval_opair rho x y :
    eval rho (opair x y) = M_opair (eval rho x) (eval rho y).
  Proof.
    reflexivity.
  Qed.

  Lemma eval_enc_bool rho b :
    eval rho (enc_bool b) = M_enc_bool b.
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma eval_prep_string rho s x :
    eval rho (prep_string s x) = M_prep_string s (eval rho x).
  Proof.
    induction s; trivial. cbn [prep_string].
    now rewrite eval_opair, IHs, eval_enc_bool.
  Qed.

  Lemma eval_enc_string rho s :
    eval rho (enc_string s) = M_enc_string s.
  Proof.
    now rewrite eval_prep_string.
  Qed.
  
  Lemma eval_enc_stack rho B :
    eval rho (enc_stack B) = M_enc_stack B.
  Proof.
    induction B; cbn; trivial. destruct a. unfold M_enc_card.
    now rewrite <- IHB, <- !eval_enc_string with (rho:=rho), <- eval_opair.
  Qed.

  Fixpoint M_enc_derivations B n :=
    match n with 
    | O => M_sing (M_opair ∅ (M_enc_stack B))
    | S n => M_enc_derivations B n ∪
            M_sing (M_opair (numeral (S n)) (M_enc_stack (derivations B (S n))))
    end.

  Lemma numeral_omega n :
    numeral n ∈ ω.
  Proof.
    induction n; cbn; now apply M_om1.
  Qed.

  Lemma binunion_el x y z :
    x ∈ y ∪ z <-> x ∈ y \/ x ∈ z.
  Proof.
    split.
    - intros [u [H1 H2]] % M_union.
      apply M_pair in H1 as [->| ->]; auto.
    - intros [H|H].
      + apply M_union. exists y. rewrite M_pair. auto.
      + apply M_union. exists z. rewrite M_pair. auto.
  Qed.

  Lemma sing_el x y :
    x ∈ M_sing y <-> x = y.
  Proof.
    split.
    - now intros [H|H] % M_pair.
    - intros ->. apply M_pair. now left.
  Qed.

  Lemma enc_derivations_base B n :
    M_opair ∅ (M_enc_stack B) ∈ M_enc_derivations B n.
  Proof.
    induction n; cbn.
    - now apply sing_el.
    - apply binunion_el. now left.
  Qed.

  Lemma opair_inj x x' y y' :
    M_opair x y = M_opair x' y' -> x = x' /\ y = y'.
  Proof.
  Admitted.

  Lemma sigma_el x y :
    x ∈ σ y <-> x ∈ y \/ x = y.
  Proof.
    split.
    - intros [H|H] % binunion_el; auto.
      apply sing_el in H. now right.
    - intros [H| ->]; apply binunion_el; auto.
      right. now apply sing_el.
  Qed.

  Lemma enc_derivations_bound B n k x :
    M_opair k x ∈ M_enc_derivations B n -> k ∈ σ (numeral n).
  Proof.
    induction n; cbn.
    - intros H % sing_el. apply opair_inj in H as [-> _].
      apply sigma_el. now right.
    - intros [H|H] % binunion_el.
      + apply sigma_el. left. apply IHn, H.
      + apply sing_el in H. apply opair_inj in H as [-> _].
        apply sigma_el. now right.
  Qed.

  Lemma numeral_wf n :
    ~ numeral n ∈ numeral n.
  Proof.
    induction n.
    - apply M_eset.
  Admitted.

  Lemma enc_derivations_fun B n :
    forall k x y, M_opair k x ∈ M_enc_derivations B n -> M_opair k y ∈ M_enc_derivations B n -> x = y.
  Proof.
    induction n; cbn -[derivations]; intros k x y.
    - intros H1 % sing_el H2 % sing_el.
      rewrite <- H2 in H1. now apply opair_inj in H1.
    - intros [H1|H1 % sing_el] % binunion_el [H2|H2 % sing_el] % binunion_el.
      + now apply (IHn k x y).
      + exfalso. apply enc_derivations_bound in H1.
        destruct (opair_inj H2) as [-> _]. now apply (@numeral_wf (S n)).
      + exfalso. apply enc_derivations_bound in H2.
        destruct (opair_inj H1) as [-> _]. now apply (@numeral_wf (S n)).
      + rewrite <- H2 in H1. now apply opair_inj in H1.
  Qed.

  Lemma enc_derivations_el B n k x :
    M_opair k x ∈ M_enc_derivations B n -> exists l, k = numeral l /\ x = M_enc_stack (derivations B l).
  Proof.
    induction n; cbn.
    - intros H % sing_el. exists 0. apply (opair_inj H).
    - intros [H|H] % binunion_el.
      + apply IHn, H.
      + apply sing_el in H. exists (S n). apply (opair_inj H).
  Qed.

  Lemma numeral_inj k l :
    numeral k = numeral l -> k = l.
  Proof.
    revert l. induction k; intros []; cbn.
    - reflexivity.
    - cbn. intros H. exfalso. apply (@M_eset (numeral n)).
      rewrite H. apply binunion_el. right. now apply sing_el.
    - cbn. intros H. exfalso. apply (@M_eset (numeral k)).
      rewrite <- H. apply binunion_el. right. now apply sing_el.
    - admit.
  Admitted.

  Lemma enc_derivations_step B n l :
    numeral l ∈ numeral n
    -> M_opair (σ (numeral l)) (M_enc_stack (derivations B (S l))) ∈ M_enc_derivations B n.
  Proof.
    induction n; cbn -[derivations].
    - now intros H % M_eset.
    - intros [H|H % sing_el] % binunion_el; apply binunion_el.
      + left. apply IHn, H.
      + right. apply numeral_inj in H as ->. now apply sing_el.
  Qed.

  Lemma binunion_eset x :
    x = ∅ ∪ x.
  Proof.
    apply M_ext.
    - intros y H. apply binunion_el. now right.
    - intros y [H|H] % binunion_el.
      + now apply M_eset in H.
      + assumption.
  Qed.

  Lemma pair_com x y :
    {x; y} = {y; x}.
  Proof.
    apply M_ext; intros z [->| ->] % M_pair; apply M_pair; auto.
  Qed.

  Lemma binunion_com x y :
    x ∪ y = y ∪ x.
  Proof.
    now rewrite pair_com.
  Qed.

  Lemma binunionl a x y :
    a ∈ x -> a ∈ x ∪ y.
  Proof.
    intros H. apply binunion_el. now left.
  Qed.

  Lemma binunionr a x y :
    a ∈ y -> a ∈ x ∪ y.
  Proof.
    intros H. apply binunion_el. now right.
  Qed.

  Hint Resolve binunionl binunionr.

  Lemma binunion_assoc x y z :
    (x ∪ y) ∪ z = x ∪ (y ∪ z).
  Proof.
    apply M_ext; intros a [H|H] % binunion_el; eauto.
    - apply binunion_el in H as [H|H]; eauto.
    - apply binunion_el in H as [H|H]; eauto.
  Qed.

  Lemma M_enc_stack_app A B :
    M_enc_stack (A ++ B) = M_enc_stack A ∪ M_enc_stack B.
  Proof.
    induction A as [|[s t] A IH]; cbn.
    - apply binunion_eset.
    - rewrite IH. rewrite !binunion_assoc.
      now rewrite (binunion_com (M_enc_stack B) (M_sing (M_enc_card s t))).
  Qed.

  Lemma enc_stack_el' x A :
    x ∈ M_enc_stack A -> exists s t, s / t el A /\ x = M_enc_card s t.
  Proof.
    induction A as [|[s t] A IH]; cbn.
    - now intros H % M_eset.
    - intros [H|H] % binunion_el.
      + destruct (IH H) as (u&v&H'&->). exists u, v. intuition.
      + apply sing_el in H as ->. exists s, t. intuition.
  Qed.

  Lemma enc_stack_el B s t :
    s / t el B -> M_enc_card s t ∈ M_enc_stack B.
  Proof.
    induction B as [|[u b] B IH]; cbn; auto.
    intros [H|H]; apply binunion_el.
    - right. apply sing_el. congruence.
    - left. apply IH, H.
  Qed.

  Lemma M_prep_enc s s' :
    M_prep_string s (M_enc_string s') = M_enc_string (s ++ s').
  Proof.
    induction s; cbn; trivial.
    now rewrite IHs.
  Qed.

  Lemma enc_stack_combinations B rho C x X Y :
    rho ⊨ combinations B X Y -> eval rho X = M_enc_stack C -> eval rho Y = x -> x = M_enc_stack (derivation_step B C).
  Proof.
    induction B as [|[s t] B IH] in rho,C,x,X,Y |-*.
    - cbn. rewrite VIEQ. now intros -> _ <-.
    - intros [x1[x2[H1[H2 H3]]]] R1 R2.
      assert (x = x2 ∪ x1) as ->. { rewrite <- R2. cbn in H1. rewrite !eval_comp in H1. apply VIEQ, H1. } clear H1.
      cbn. fold (derivation_step B C). rewrite M_enc_stack_app.
      enough (x1 = M_enc_stack (derivation_step B C)) as E1.
      + enough (x2 = M_enc_stack (append_all C (s / t))) as E2 by now rewrite E1, E2.
        apply M_ext; intros u Hu.
        * apply H3 in Hu as [v [Hv[a [b Ha]]]].
          cbn in Hv. rewrite !eval_comp, R1 in Hv. apply enc_stack_el' in Hv as (s'&t'&H&H').
          enough (u = M_enc_card (s++s') (t++t')) as ->.
          { apply enc_stack_el. apply in_map_iff. now exists (s'/t'). }
          cbn in Ha. rewrite !VIEQ in Ha. destruct Ha as [D1 D2].
          rewrite D1 in H'. unfold M_enc_card in H'. apply opair_inj in H' as [-> ->].
          rewrite D2; unfold M_enc_card, M_opair; repeat f_equal.
          all: rewrite eval_prep_string; cbn. all: apply M_prep_enc.
        * apply enc_stack_el' in Hu as (s'&t'&H&->).
          unfold append_all in H. eapply in_map_iff in H as [[a b][H H']].
          cbn in H. apply H3. exists (M_enc_card a b). split.
          { cbn. rewrite !eval_comp, R1. now apply enc_stack_el. }
          exists (M_enc_string b), (M_enc_string a). split.
          -- cbn. apply VIEQ. reflexivity.
          -- cbn. apply VIEQ. rewrite !eval_prep_string. cbn.
             rewrite !M_prep_enc. injection H. intros -> ->. reflexivity.
      + eapply IH; eauto. now rewrite !eval_comp, R1.
  Qed.

  Lemma derivations_enc_derivations B n :
    M_opair (numeral n) (M_enc_stack (derivations B n)) ∈ M_enc_derivations B n.
  Proof.
    induction n; cbn -[derivations].
    - now apply sing_el.
    - apply binunion_el. right.
      now apply sing_el.
  Qed.

  Lemma derivations_el B n s t :
     s / t el derivations B n -> M_enc_card s t ∈ M_enc_stack (derivations B n).
  Proof.
    apply enc_stack_el.
  Qed.

  Theorem PCP_ZF1 B s :
    derivable B s s -> forall rho, rho ⊨ solvable B.
  Proof.
    intros H rho. destruct (derivable_derivations H) as [n Hn]. unfold solvable.
    exists (numeral n), (M_enc_derivations B n), (M_opair (M_enc_string s) (M_enc_string s)).
    exists (M_enc_string s), (M_enc_stack (derivations B n)). repeat split.
    - apply numeral_omega.
    - unfold function'. intros k x y H1 H2. apply VIEQ. apply (enc_derivations_fun H1 H2).
    - specialize (enc_derivations_base B n). intros HB.
      erewrite <- eval_enc_stack in HB. apply HB.
    - intros k x x' H1' H2' H3.
      assert (H1 : k ∈ numeral n) by apply H1'. clear H1'.
      assert (H2 : M_opair k x ∈ M_enc_derivations B n) by apply H2'. clear H2'.
      destruct (enc_derivations_el H2) as [l[-> ->]].
      specialize (enc_derivations_step B H1).
      replace (M_enc_stack (derivations B (S l))) with x'; trivial.
      apply (enc_stack_combinations H3); trivial.
    - apply derivations_enc_derivations.
    - now apply enc_stack_el.
    - cbn. apply VIEQ. reflexivity.
  Qed.

  Print Assumptions PCP_ZF1.

  Definition M_comb_rel s t :=
    fun u v => exists u1 u2, u = M_opair u1 u2 /\ v = M_opair (M_prep_string s u1) (M_prep_string t u2).

  Fixpoint M_combinations B x y :=
    match B with
    | nil => y = ∅
    | (s,t)::B => exists y1 y2, y = y2 ∪ y1 /\ M_combinations B x y1 /\ M_is_rep (M_comb_rel s t) x y2
    end.

  Lemma M_combinations_spec B rho x y a b :
    M_combinations B x y -> eval rho a = x -> eval rho b = y -> rho ⊨ combinations B a b.
  Proof.
    induction B in y,a,b,rho|-*; cbn.
    - rewrite VIEQ. now intros -> _ ->.
    - destruct a0 as [s t]. intros (y1&y2&H1&H2&H3) Ha Hb. exists y1, y2.
      split. { cbn. apply VIEQ. erewrite !eval_comp. now rewrite Hb. }
      split. { eapply (IHB _ y1); trivial. erewrite !eval_comp. now rewrite Ha. }
      intros v. split.
      + intros (u&Hu&c&d&H) % H3. exists u. split.
        * cbn. erewrite !eval_comp. rewrite Ha. apply Hu.
        * exists d, c. cbn. rewrite !VIEQ, !eval_prep_string. apply H.
      + intros (u&Hu&c&d&H). apply H3. exists u. split.
        * cbn in Hu. erewrite !eval_comp in Hu. rewrite <- Ha. apply Hu.
        * exists d, c. cbn in H. rewrite !VIEQ, !eval_prep_string in H. apply H.
  Qed.

  Lemma M_comb_rel_ex s t x :
    exists y, M_is_rep (M_comb_rel s t) x y.
  Proof.
    apply M_rep.
    - exists (comb_rel s t). split.
      + repeat constructor; admit.
      + intros u v rho. cbn. admit.
    - intros a b b' (u&v&H1&H2) (u'&v'&H3&H4); subst.
      now apply opair_inj in H3 as [-> ->].
  Admitted.

  Definition M_solutions B f n :=
    M_opair ∅ (M_enc_stack B) ∈ f /\ forall k x y, k ∈ n -> M_opair k x ∈ f -> M_combinations B x y -> M_opair (σ k) y ∈ f.

  Lemma is_rep_unique R x y y' :
    M_is_rep R x y -> M_is_rep R x y' -> y = y'.
  Proof.
    intros H1 H2. apply M_ext; intros v.
    - intros H % H1. now apply H2.
    - intros H % H2. now apply H1.
  Qed. 

  Lemma comb_rel_rep C s t :
    M_is_rep (M_comb_rel s t) (M_enc_stack C) (M_enc_stack (append_all C (s / t))).
  Proof.
    intros y. split.
    - intros (u&v&H&->) % enc_stack_el'.
      unfold append_all in H. apply in_map_iff in H as [[a b][H1 H2]]. cbn in H1.
      exists (M_enc_card a b). split; try now apply enc_stack_el.
      exists (M_enc_string a), (M_enc_string b). split; trivial.
      assert (u = s++a) as -> by congruence. assert (v = t++b) as -> by congruence.
      now rewrite !M_prep_enc.
    - intros (u&H&a&b&->&->). apply enc_stack_el' in H as [u[v[H1 H2]]].
      apply opair_inj in H2 as [-> ->]. rewrite !M_prep_enc. apply enc_stack_el.
      apply in_map_iff. now exists (u/v).
  Qed.

  Lemma M_combinations_step B C :
    M_combinations B (M_enc_stack C) (M_enc_stack (derivation_step B C)).
  Proof.
    induction B as [|[s t] B IH]; cbn; trivial.
    destruct (M_comb_rel_ex s t (M_enc_stack C)) as [y2 Hy2].
    exists (M_enc_stack (derivation_step B C)), y2. split; try now split.
    enough (y2 = M_enc_stack (append_all C (s / t))) as -> by apply M_enc_stack_app.
    apply (is_rep_unique Hy2). apply comb_rel_rep.
  Qed.

  Lemma numeral_mon k n :
    k < n -> numeral k ∈ numeral n.
  Proof.
    induction 1; cbn; apply sigma_el; auto.
  Qed.

  Lemma solutions_derivations B f n k :
    M_solutions B f (numeral n) -> k <= n -> M_opair (numeral k) (M_enc_stack (derivations B k)) ∈ f.
  Proof.
    intros H Hk; induction k; cbn.
    - apply H.
    - assert (Hk' : k <= n) by lia. specialize (IHk Hk').
      destruct H as [_ H]. eapply H in IHk; eauto.
      + now apply numeral_mon.
      + apply M_combinations_step.
  Qed.

  Lemma derivations_derivable B n s t :
    s / t el derivations B n -> derivable B s t.
  Proof.
    induction n in s,t|-*; cbn.
    - now constructor.
    - unfold derivation_step. intros [[u v][H1 H2]] % in_flat_map.
      unfold append_all in H2. apply in_map_iff in H2 as [[a b][H2 H3]]. cbn in H2.
      assert (s = u++a) as -> by congruence. assert (t = v++b) as -> by congruence.
      constructor 2; trivial. apply IHn, H3.
  Qed.

  Lemma M_solutions_el B f n k X p :
    M_function f -> M_solutions B f (numeral n) -> M_opair (numeral k) X ∈ f
    -> k <= n -> p ∈ X -> exists u v, p = M_enc_card u v /\ derivable B u v.
  Proof.
    intros Hf Hn HX Hk Hp. apply (solutions_derivations Hn) in Hk.
    rewrite (Hf _ _ _ HX Hk) in Hp. apply enc_stack_el' in Hp as (s&t&H&->).
    exists s, t. split; trivial. eapply derivations_derivable; eauto.
  Qed.

  Hypothesis VIN : forall n, n ∈ ω -> exists k, n = numeral k.

  Lemma enc_bool_inj b c :
    M_enc_bool b = M_enc_bool c -> b = c.
  Proof.
    destruct b, c; trivial; cbn.
    - intros H. contradiction (@M_eset ∅).
      pattern ∅ at 2. rewrite <- H. apply M_pair; auto.
    - intros H. contradiction (@M_eset ∅).
      pattern ∅ at 2. rewrite H. apply M_pair; auto.
  Qed.

  Lemma enc_string_inj s t :
    M_enc_string s = M_enc_string t -> s = t.
  Proof.
    induction s in t|-*; destruct t as [|b t]; cbn; trivial.
    - intros H. contradiction (M_eset (x:=M_sing (M_enc_bool b))).
      rewrite H. apply M_pair. now left.
    - intros H. contradiction (M_eset (x:=M_sing (M_enc_bool a))).
      rewrite <- H. apply M_pair. now left.
    - intros [H1 H2] % opair_inj. apply IHs in H2 as ->.
      apply enc_bool_inj in H1 as ->. reflexivity.
  Qed.

  Theorem PCP_ZF2 B rho :
    rho ⊨ solvable B -> exists s, derivable B s s.
  Proof.
    intros (n&f&p&s&X&H1&H2&H3&H4&H5&H6).
    assert (H1' : n ∈ ω) by apply H1. clear H1.
    assert (H6' : p = M_opair s s) by apply VIEQ, H6. clear H6.
    assert (H4' : M_opair n X ∈ f) by apply H4. clear H4.
    assert (H5' : p ∈ X) by apply H5. clear H5.
    assert (H2' : M_function f).
    { intros x y y' H H'. apply VIEQ. eapply H2. apply H. apply H'. } clear H2.
    assert (H3' : M_opair ∅ (M_enc_stack B) ∈ f).
    { erewrite <- eval_enc_stack. apply H3. } destruct H3 as [_ H3].
    assert (H3'' : forall k x y, k ∈ n -> M_opair k x ∈ f -> M_combinations B x y -> M_opair (σ k) y ∈ f).
    { intros k x y Hn Hk Hy. apply (H3 k x y); auto. fold sat. eapply M_combinations_spec; eauto. } clear H3.
    destruct (VIN H1') as [l ->]. destruct (@M_solutions_el B f l l X p) as (u&v&->&H2); trivial. now split.
    exists u. apply opair_inj in H6' as [<- H]. apply enc_string_inj in H as ->. apply H2.
  Qed.

  Print Assumptions PCP_ZF2.
  
End ZF.
