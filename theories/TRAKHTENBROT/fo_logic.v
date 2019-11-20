(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms.

Set Implicit Arguments.

Notation ø := vec_nil.

Opaque fo_term_subst fo_term_map fo_term_sem.

Record fo_signature := Mk_fo_signature {
  syms : Type;
  rels : Type;
  ar_syms : syms -> nat;
  ar_rels : rels -> nat
}.

(** Unscoped (nat) DeBruijn syntax for FOL formulas *)

Inductive fol_form (Σ : fo_signature) : Type :=
  | fol_false : fol_form Σ
  | fol_atom  : forall p, vec (fo_term nat (ar_syms Σ)) (ar_rels Σ p) -> fol_form Σ 
  | fol_bin   : fol_bop -> fol_form Σ -> fol_form Σ -> fol_form Σ 
  | fol_quant : fol_qop -> fol_form Σ -> fol_form Σ. 

Infix "⤑" := (fol_bin fol_imp) (at level 62, right associativity).
Infix "⟑" := (fol_bin fol_conj) (at level 60, right associativity).
Infix "⟇" := (fol_bin fol_disj) (at level 61, right associativity).
Notation "∀ f" := (fol_quant fol_fa f) (at level 64, right associativity).
Notation "∃ f" := (fol_quant fol_ex f) (at level 64, right associativity).

Notation "x ↔ y" := ((x⤑y)⟑(y⤑x)) (at level 63, no associativity).

Notation "£" := ((@in_var nat _ _) : nat -> fo_term nat _).
Notation "⊥" := (fol_false _).

Section fol_subst.

  Variable (Σ : fo_signature).

  Notation 𝕋 := (fo_term nat (ar_syms Σ)).
  Notation 𝔽 := (fol_form Σ).

  (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ρ ↑ ⦃ ⦄ ⇡*)

  Fixpoint fol_vars (A : 𝔽) :=
    match A with
      | ⊥              => nil
      | fol_atom _ p v => flat_map (@fo_term_vars _ _ _) (vec_list v)
      | fol_bin c A B => fol_vars A ++ fol_vars B
      | fol_quant q A => flat_map (fun n => match n with 0 => nil | S n => n::nil end)
                           (fol_vars A) 
    end.

  Fixpoint fol_syms (A : 𝔽) :=
    match A with
      | ⊥              => nil
      | fol_atom _ p v => flat_map (@fo_term_syms _ _ _) (vec_list v)
      | fol_bin c A B  => fol_syms A ++ fol_syms B
      | fol_quant q A  => fol_syms A 
    end.

  Fixpoint fol_rels (A : 𝔽) :=
    match A with
      | ⊥              => nil
      | fol_atom _ p v => p::nil
      | fol_bin c A B  => fol_rels A ++ fol_rels B
      | fol_quant q A  => fol_rels A 
    end.

  Fixpoint fol_subst σ (A : 𝔽) :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ p v => fol_atom _ _ (vec_map (fo_term_subst σ) v)
      | fol_bin c A B => fol_bin c (A⦃σ⦄) (B⦃σ⦄)
      | fol_quant q A => fol_quant q (A⦃⇡σ⦄) 
    end
  where "A ⦃ σ ⦄" := (fol_subst σ A).

  Fact fol_subst_ext σ ρ A : 
       (forall n, In n (fol_vars A) -> σ n = ρ n) -> A⦃σ⦄ = A⦃ρ⦄.
  Proof.
    intros Hfg; revert A σ ρ Hfg. 
    induction A as [ | p v | c A IHA B IHB | q A IHA ]; intros f g Hfg; simpl; f_equal; auto.
    + apply vec_map_ext; intros t Ht. 
      apply fo_term_subst_ext; intros n Hn.
      apply Hfg, in_flat_map; exists t; split; auto.
      apply in_vec_list; auto.
    + apply IHA; intros n Hn; apply Hfg, in_or_app; auto.
    + apply IHB; intros n Hn; apply Hfg, in_or_app; auto.
    + apply IHA; intros [ | n ] Hn; simpl; auto.
      rew fot.
      f_equal; apply Hfg; simpl.
      apply in_flat_map; exists (S n); simpl; auto. 
  Qed.

  Fact fol_vars_subst σ (A : 𝔽) : fol_vars (A⦃σ⦄) = flat_map (fun x => fo_term_vars (σ x)) (fol_vars A).
  Proof.
    revert σ; induction A as [ | s r | b A HA B HB | q A HA ]; intros phi; auto.
    + simpl fol_vars.
      rewrite vec_list_vec_map.
      rewrite flat_map_flat_map.
      do 2 rewrite flat_map_concat_map.
      rewrite map_map; f_equal.
      apply map_ext; intros x.
      rewrite fo_term_vars_subst; auto.
    + simpl; rewrite flat_map_app; f_equal; auto.
    + simpl; rewrite HA.
      do 2 rewrite flat_map_flat_map.
      do 2 rewrite flat_map_concat_map; f_equal.
      apply map_ext_in; intros [ | x ] Hx; simpl; auto.
      rewrite fo_term_vars_map; rew fot.
      rewrite flat_map_concat_map, map_map.
      rewrite <- flat_map_concat_map.
      rewrite <- app_nil_end.
      rewrite flat_map_single, map_id; auto.
  Qed.

  Fact fol_vars_map σ (A : 𝔽) : fol_vars (A⦃fun n => £(σ n)⦄) = map σ (fol_vars A).
  Proof. rewrite fol_vars_subst, <- flat_map_single; auto. Qed.

  Fact fol_syms_subst P σ (A : 𝔽) : 
        (forall n, In n (fol_vars A) -> Forall P (fo_term_syms (σ n)))  
     -> Forall P (fol_syms A) -> Forall P (fol_syms (A⦃σ⦄)).
  Proof.
    revert σ.
    induction A as [ | s r | b A HA B HB | q A HA ]; intros f Hf H; simpl; auto.
    + rewrite Forall_forall in H |- *.
      intros s'; rewrite in_flat_map.
      intros (t & Ht); revert Ht.
      rewrite vec_list_vec_map, in_map_iff.
      intros ((t' & <- & H1) & H2).
      revert s' H2; apply Forall_forall.
      apply fo_term_syms_subst.
      simpl in H, Hf.
      * intros n Hn; apply Hf, in_flat_map.
        exists t'; auto.
      * apply Forall_forall; intros s' Hs'.
        apply H, in_flat_map; exists t'; auto.
    + simpl in H; rewrite Forall_app in H.
      rewrite Forall_app; split.
      * apply HA; try tauto.
        intros; apply Hf, in_or_app; auto.
      * apply HB; try tauto.
        intros; apply Hf, in_or_app; auto.
    + simpl in H; apply HA; auto.
      intros [ | n ]; simpl; rew fot; auto.
      rewrite fo_term_syms_map; intros Hn. 
      apply Hf, in_flat_map.
      exists (S n); simpl; auto.
  Qed.

  Fact fol_rels_subst σ (A : 𝔽) : fol_rels (A⦃σ⦄) = fol_rels A.
  Proof.
    revert σ.
    induction A as [ | s r | b A HA B HB | q A HA ]; intros f; simpl; auto.
    rewrite HA, HB; auto.
  Qed.

  Definition fol_bigop c A := fold_right (@fol_bin Σ c) A.

  Fact fol_syms_bigop c l A : fol_syms (fol_bigop c A l) = flat_map fol_syms l++fol_syms A.
  Proof. 
    induction l; simpl; auto.
    rewrite app_ass; f_equal; auto.
  Qed.

  Fact fol_rels_bigop c l A : fol_rels (fol_bigop c A l) = flat_map fol_rels l++fol_rels A.
  Proof. 
    induction l; simpl; auto.
    rewrite app_ass; f_equal; auto.
  Qed.

  Fact fol_subst_bigop c l A σ : (fol_bigop c A l)⦃σ⦄ = fol_bigop c (A⦃σ⦄) (map (fol_subst σ) l).
  Proof. induction l; simpl; f_equal; auto. Qed.

  (** ∀ ... ∀ A  and  ∃ ... ∃ A *)

  Fixpoint fol_mquant q n (A : 𝔽) := 
    match n with 
      | 0   => A
      | S n => fol_quant q (fol_mquant q n A)
    end.

  Fact fol_mquant_plus q a b A : fol_mquant q (a+b) A = fol_mquant q a (fol_mquant q b A).
  Proof. induction a; simpl; f_equal; auto. Qed.
  
  Fact fol_mquant_S q n A : fol_mquant q (S n) A = fol_mquant q n (fol_quant q A).
  Proof. 
    replace (S n) with (n+1) by lia.
    apply fol_mquant_plus.
  Qed.

  (** (Free) variables in ∀ ... ∀ A  and  ∃ ... ∃ A *)

  Fact fol_vars_mquant q n (A : 𝔽) :
        fol_vars (fol_mquant q n A)
      = flat_map (fun i => if le_lt_dec n i then (i-n::nil) else nil) (fol_vars A).
  Proof.
    revert A; induction n as [ | n IHn ]; intros A.
    + simpl; rewrite <- map_id at 1; rewrite <- flat_map_single.
      do 2 rewrite flat_map_concat_map; f_equal; apply map_ext.
      intro a; destruct (le_lt_dec 0 a); f_equal; lia.
    + rewrite fol_mquant_S. 
      rewrite IHn; simpl fol_vars; rewrite flat_map_flat_map.
      do 2 rewrite flat_map_concat_map; f_equal; apply map_ext.
      intros [ | a ]; auto; simpl flat_map.
      rewrite <- app_nil_end.
      destruct (le_lt_dec n a); destruct (le_lt_dec (S n) (S a)); auto; lia.
  Qed.
 
  Fact fol_syms_mquant q n A : fol_syms (fol_mquant q n A) = fol_syms A.
  Proof. induction n; simpl; auto. Qed.

  Fact fol_rels_mquant q n A : fol_rels (fol_mquant q n A) = fol_rels A.
  Proof. induction n; simpl; auto. Qed.

  (** This theorem is the important one that shows substitutions do compose 
      hence De Bruijn notation are handled correctly by substitutions *)

  Fact fol_subst_subst σ ρ A : A⦃σ⦄⦃ρ⦄ = A⦃fun n => (σ n)⟬ρ⟭⦄.
  Proof.
    revert σ ρ; induction A 
        as [ | p v | b A IHA B IHB | q A IHA ]; 
        simpl; intros f g; auto.
    + f_equal.
      rewrite vec_map_map.
      apply vec_map_ext.
      intros A w; rew fot; auto. 
    + f_equal; auto.
    + f_equal.
      rewrite IHA; auto.
      apply fol_subst_ext.
      intros [ | n ] _; rew fot; simpl; rew fot; simpl; auto.
      do 2 rewrite <- fo_term_subst_map, fo_term_subst_comp.
      apply fo_term_subst_ext.
      intros; rew fot; rewrite fo_term_subst_map; simpl; rew fot; auto.
  Qed.

End fol_subst.

Notation "A ⦃ σ ⦄" := (fol_subst σ A).

Record fo_model Σ (X : Type) := {
  fom_syms : forall s, vec X (ar_syms Σ s) -> X;
  fom_rels : forall s, vec X (ar_rels Σ s) -> Prop }.

Section fol_semantics.

  Variable (Σ : fo_signature) (X : Type) (M : fo_model Σ X).

  Notation sem_sym := (fom_syms M _).
  Notation sem_pred := (fom_rels M _).

  Implicit Type φ : nat -> X.

  Notation "⟦ t ⟧" := (fun φ => fo_term_sem (fom_syms M) φ t).

  (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ↑ *)

  Fixpoint fol_sem φ A : Prop :=
      match A with
        | ⊥              => False
        | fol_atom _ _ v => sem_pred (vec_map (fun t => ⟦t⟧ φ) v)
        | fol_bin b A B  => fol_bin_sem b (⟪A⟫ φ) (⟪B⟫ φ) 
        | fol_quant q A  => fol_quant_sem q (fun x => ⟪A⟫ (φ↑x))
      end
    where "⟪ A ⟫" := (fun φ => fol_sem φ A).

  Definition fol_ldisj := @fol_bigop Σ fol_disj ⊥.
  Definition fol_lconj := @fol_bigop Σ fol_conj (⊥⤑⊥).

  Fact fol_sem_big_disj lf φ : ⟪ fol_ldisj lf ⟫ φ <-> exists f, In f lf /\ ⟪ f ⟫ φ.
  Proof.
    induction lf as [ | f lf IHlf ]; simpl.
    + split; try tauto; intros ( ? & [] & _).
    + rewrite IHlf.
      split.
      * intros [ H | (g & H1 & H2) ].
        - exists f; auto.
        - exists g; auto.
      * intros (g & [ <- | Hg ] & ?); auto.
        right; exists g; auto.
  Qed.

  Fact fol_sem_big_conj lf φ : ⟪ fol_lconj lf ⟫ φ <-> forall f, In f lf -> ⟪ f ⟫ φ.
  Proof.
    induction lf as [ | f lf IHlf ]; simpl.
    + split; tauto.
    + rewrite IHlf.
      split.
      * intros [] ? [ -> | ]; auto.
      * intros H; split; intros; apply H; auto.
  Qed.

  Fixpoint env_vlift φ n (v : vec X n) :=
    match v with
      | ø    => φ
      | x##v => (env_vlift φ v)↑x
    end.

  Fact env_vlift_fix0 φ n (v : vec X n) p : env_vlift φ v (pos2nat p) = vec_pos v p.
  Proof.
    revert φ p; induction v as [ | n x v IHv ]; intros phi p; auto.
    + invert pos p.
    + invert pos p.
      * rewrite pos2nat_fst; auto.
      * rewrite pos2nat_nxt; simpl; auto.
  Qed.

  Fact env_vlift_fix1 φ n (v : vec X n) k : env_vlift φ v (k+n) = φ k.
  Proof.
    revert φ k; induction v as [ | n x v IHv ]; intros phi k; simpl; auto.
    replace (k+S n) with (S (k+n)) by lia; simpl; auto.
  Qed.

  (** The semantics of ∀ ... ∀ A *)

  Fact fol_sem_mforall n A φ : ⟪fol_mquant fol_fa n A⟫ φ 
                           <-> forall v : vec X n, ⟪A⟫ (env_vlift φ v).
  Proof.
    revert A φ; induction n as [ | n IHn ]; intros A phi.
    + split.
      * intros H v; vec nil v; simpl; auto.
      * intros H; apply (H ø).
    + rewrite fol_mquant_S, IHn; split.
      * intros H v; vec split v with x; apply (H v).
      * intros H v; intros x; apply (H (x##v)).
  Qed.

  (** The semantics of ∃ ... ∃ A *)

  Fact fol_sem_mexists n A φ : ⟪fol_mquant fol_ex n A⟫ φ 
                           <-> exists v : vec X n, ⟪A⟫ (env_vlift φ v).
  Proof.
    revert A φ; induction n as [ | n IHn ]; intros A phi.
    + split.
      * intros H; exists ø; auto.
      * intros (v & Hv); revert Hv; vec nil v; auto.
    + rewrite fol_mquant_S, IHn; split.
      * intros (v & x & Hv).
        exists (x##v); auto.
      * intros (v & Hv); revert Hv; vec split v with x.
        exists v, x; auto.
  Qed.

  (** Semantics depends only on occuring variables *)

  Fact fol_sem_ext φ ψ A : (forall n, In n (fol_vars A) -> φ n = ψ n) -> ⟪A⟫ φ <-> ⟪A⟫ ψ.
  Proof.
    intros H; revert A φ ψ H.
    induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros phi psy H; try tauto.
    + match goal with | |- sem_pred ?x <-> sem_pred ?y => replace y with x; try tauto end.
      apply vec_map_ext; intros w Hw. 
      apply fo_term_sem_ext; auto.
      intros n Hn; apply H, in_flat_map; exists w; split; auto.
      apply in_vec_list; auto.
    + apply fol_bin_sem_ext.
      * apply IHA; intros; apply H, in_or_app; auto.
      * apply IHB; intros; apply H, in_or_app; auto.
    + apply fol_quant_sem_ext.
      intros x; apply IHA.
      intros [ | n] Hn; simpl; auto; apply H, in_flat_map.
      exists (S n); simpl; auto.
  Qed.

  (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ↑ ⦃ ⦄*)

  (** Semantics commutes with substitutions ... good *)

  Theorem fol_sem_subst φ σ A : ⟪ A⦃σ⦄ ⟫ φ <-> ⟪A⟫ (fun n => ⟦σ n⟧ φ).
  Proof.
    revert φ σ; induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros phi f; try tauto.
    + match goal with | |- sem_pred ?x <-> sem_pred ?y => replace y with x; try tauto end.
      rewrite vec_map_map; apply vec_map_ext.
      intros; rewrite fo_term_sem_subst; auto.
    + apply fol_bin_sem_ext; auto.
    + apply fol_quant_sem_ext.
      intros x; rewrite IHA.
      apply fol_sem_ext. 
      intros [ | n ] _; simpl; rew fot; simpl; auto.
      rewrite <- fo_term_subst_map; rew fot.
      apply fo_term_sem_ext; intros; rew fot; auto.
  Qed.

  Definition fo_model_dec := forall s (v : vec _ (ar_rels _ s)), { sem_pred v } + { ~ sem_pred v }.

  Section decidable.

    (** REMARK: not requiring the sem_pred relation to be decidable
        would allow hiding uncomputability inside the model which
        would be kind of cheating. The semantic relation should be
        decidable, only the (finite) satisfiability relation should 
        be undec *)

    (** For the semantics relation to be decidable over a finite domain,
        it is necessary and SUFFICIENT that the sem_pred relation is decidable
       or equivalently, each predicate is interpreted as a map: vec X _ -> bool *)

    Variable (M_fin : finite_t X).
    Variable (rels_dec : fo_model_dec).

    Theorem fol_sem_dec A φ : { ⟪A⟫ φ } + { ~ ⟪A⟫ φ }.
    Proof.
      revert φ.
      induction A as [ | p v | b A IHA B IHB | q A IHA ]; intros phi.
      + simpl; tauto.
      + simpl; apply rels_dec.
      + simpl fol_sem; apply fol_bin_sem_dec; auto.
      + simpl fol_sem; apply fol_quant_sem_dec; auto.
    Qed.

  End decidable.

End fol_semantics.

Section fo_model_simulation.

  (** We state a general simulation result for models on a given 
      formula build on a bounded list of symbols. The statement
      is so general that the proof is just obvious ;-) *)

  Variables  (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
             (X : Type) (M : fo_model Σ X)
             (Y : Type) (N : fo_model Σ Y)
             (R : X -> Y -> Prop).

  Infix "⋈" := R (at level 70, no associativity). 

  Hypothesis (Hs : forall s v w, In s ls 
                              -> (forall p, vec_pos v p ⋈ vec_pos w p)
                              -> fom_syms M s v ⋈ fom_syms N s w)
             (Hr : forall s v w, In s lr 
                              -> (forall p, vec_pos v p ⋈ vec_pos w p)
                              -> fom_rels M s v <-> fom_rels N s w).
  
  Notation "⟦ t ⟧" := (fun φ => fo_term_sem (fom_syms M) φ t).
  Notation "⟦ t ⟧'" := (fun φ => fo_term_sem (fom_syms N) φ t) (at level 1, format "⟦ t ⟧'").

  Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
  Notation "⟪ A ⟫'" := (fun φ => fol_sem N φ A) (at level 1, format "⟪ A ⟫'").

  Let fo_term_simulation t φ ψ :
           (forall n : nat, In n (fo_term_vars t) -> φ n ⋈ ψ n) 
        -> incl (fo_term_syms t) ls
        -> ⟦t⟧ φ ⋈ ⟦t⟧' ψ.
  Proof.
    revert φ ψ.
    induction t as [ k | s v IH ]; intros phi psi Hv Hls; rew fot; auto.
    + apply Hv; simpl; auto.
    + apply Hs.
      * apply Hls; simpl; auto.
      * intros p; do 2 rewrite vec_pos_map.
        apply IH.
        - apply in_vec_pos.
        - intros n Hn.
          apply Hv; rew fot.
          apply in_flat_map.
          exists (vec_pos v p); split; auto.
          apply in_vec_list, in_vec_pos.
        - apply incl_tran with (2 := Hls).
          intros s' Hs'; rew fot.
          right; apply in_flat_map.
          exists (vec_pos v p); split; auto.
          apply in_vec_list, in_vec_pos.
  Qed.

  Hypothesis (Hsim1 : forall x, exists y, x ⋈ y)
             (Hsim2 : forall y, exists x, x ⋈ y).

  Theorem fo_model_simulation A φ ψ :
           (forall n : nat, In n (fol_vars A) -> φ n ⋈ ψ n) 
        -> incl (fol_syms A) ls
        -> incl (fol_rels A) lr
        -> ⟪A⟫ φ <-> ⟪A⟫' ψ.
  Proof.
    revert φ ψ.
    induction A as [ | r | b A HA B HB | q A HA ]; intros phi psi Hp Hs1 Hr1; simpl; try tauto.
    + apply Hr.
      * apply Hr1; simpl; auto.
      * intros p; do 2 rewrite vec_pos_map.
        apply fo_term_simulation.
        - intros n Hn; apply Hp; simpl.
          apply in_flat_map.
          exists (vec_pos v p); split; auto.
          apply in_vec_list, in_vec_pos.
        - apply incl_tran with (2 := Hs1).
          intros s' Hs'; simpl.
          apply in_flat_map.
          exists (vec_pos v p); split; auto.
          apply in_vec_list, in_vec_pos.
    + apply fol_bin_sem_ext; [ apply HA | apply HB ].
      1,4: intros; apply Hp; simpl; apply in_or_app; auto.
      1,3: apply incl_tran with (2 := Hs1); intros ? ?; apply in_or_app; auto.
      1,2: apply incl_tran with (2 := Hr1); intros ? ?; apply in_or_app; auto.
    + destruct q; simpl; split.
      * intros (x & Hx).
        destruct (Hsim1 x) as (y & Hy); exists y.
        revert Hx; apply HA.
        - intros []; simpl; auto.
          intros; apply Hp, in_flat_map.
          exists (S n); simpl; auto.
        - apply incl_tran with (2 := Hs1), incl_refl.
        - apply incl_tran with (2 := Hr1), incl_refl.
      * intros (y & Hy).
        destruct (Hsim2 y) as (x & Hx); exists x.
        revert Hy; apply HA.
        - intros []; simpl; auto.
          intros; apply Hp, in_flat_map.
          exists (S n); simpl; auto.
        - apply incl_tran with (2 := Hs1), incl_refl.
        - apply incl_tran with (2 := Hr1), incl_refl.
      * intros H y.
        destruct (Hsim2 y) as (x & Hx).
        generalize (H x); apply HA.
        - intros []; simpl; auto.
          intros; apply Hp, in_flat_map.
          exists (S n); simpl; auto.
        - apply incl_tran with (2 := Hs1), incl_refl.
        - apply incl_tran with (2 := Hr1), incl_refl.
      * intros H x.
        destruct (Hsim1 x) as (y & Hy).
        generalize (H y); apply HA.
        - intros []; simpl; auto.
          intros; apply Hp, in_flat_map.
          exists (S n); simpl; auto.
        - apply incl_tran with (2 := Hs1), incl_refl.
        - apply incl_tran with (2 := Hr1), incl_refl.
  Qed.

End fo_model_simulation.

Check fo_model_simulation.

Section fo_model_projection.

  (** We specialize the previous simulation result on simulation
      obtained as surjective projections *)

  Variable (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
           (X : Type) (M : fo_model Σ X) (φ : nat -> X) 
           (Y : Type) (N : fo_model Σ Y) (ψ : nat -> Y)
           (i : X -> Y) (j : Y -> X) (E : forall x, i (j x) = x)
           (Hs : forall s v, In s ls -> i (fom_syms M s v) = fom_syms N s (vec_map i v))
           (Hr : forall s v, In s lr -> fom_rels M s v <-> fom_rels N s (vec_map i v)).

  Theorem fo_model_projection A : 
           (forall n, In n (fol_vars A) -> i (φ n) = ψ n)
        -> incl (fol_syms A) ls 
        -> incl (fol_rels A) lr
        -> fol_sem M φ A <-> fol_sem N ψ A.
  Proof.
    apply fo_model_simulation with (R := fun x y => i x = y).
    + intros s v w Hs1 H; rewrite Hs; auto.
      f_equal; apply vec_pos_ext; intros; rewrite vec_pos_map; auto.
    + intros s v w Hr1 H; rewrite Hr; auto.
      match goal with |- ?x <-> ?y => cut (x = y); [ intros ->; tauto | ] end.
      f_equal; apply vec_pos_ext; intros; rewrite vec_pos_map; auto.
    + intros x; exists (i x); auto.
    + intros y; exists (j y); auto.
  Qed.

End fo_model_projection.

Check fo_model_projection.

Section fo_definability.

  Variable (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
           (X : Type) (M : fo_model Σ X).

  Definition fot_definable (f : (nat -> X) -> X) := 
       { t | incl (fo_term_syms t) ls /\ forall φ, fo_term_sem (fom_syms M) φ t = f φ }.

  Definition fol_definable (R : (nat -> X) -> Prop) :=
       { A | incl (fol_syms A) ls 
          /\ incl (fol_rels A) lr 
          /\ forall φ, fol_sem M φ A <-> R φ }.

  Fact fot_def_proj n : fot_definable (fun φ => φ n).
  Proof. exists (£ n); intros; split; rew fot; auto; intros _ []. Qed.

  Fact fot_def_comp s v : 
        In s ls
      -> (forall p, fot_definable (fun φ => vec_pos (v φ) p))
      -> fot_definable (fun φ => fom_syms M s (v φ)).
  Proof.
    intros H0 H; apply vec_reif_t in H.
    destruct H as (w & Hw).
    exists (@in_fot nat _ _ _ w); split; rew fot.
    + intros x [ -> | H ]; auto; revert H.
      rewrite in_flat_map.
      intros (t & H1 & H2).
      apply in_vec_list, in_vec_inv in H1.
      destruct H1 as (p & <- ).
      revert H2; apply Hw.
    + intros phi; rew fot; f_equal.
      apply vec_pos_ext; intros p.
      rewrite vec_pos_map.
      apply Hw; auto.
  Qed.

  Fact fot_def_equiv f g : 
         (forall φ, f φ = g φ) -> fot_definable f -> fot_definable g.
  Proof.
    intros E (t & H1 & H2); exists t; split; auto; intro; rewrite H2; auto.
  Qed.

  Fact fol_def_atom r v :
         In r lr
      -> (forall p, fot_definable (fun φ => vec_pos (v φ) p))
      -> fol_definable (fun φ => fom_rels M r (v φ)).
  Proof.
    intros H0 H; apply vec_reif_t in H.
    destruct H as (w & Hw).
    exists (@fol_atom _ _ w); msplit 2.
    + simpl; intro s; rewrite in_flat_map.
      intros (t & H1 & H2).
      apply in_vec_list, in_vec_inv in H1.
      destruct H1 as (p & <- ).
      revert H2; apply Hw.
    + simpl; intros ? [ -> | [] ]; auto.
    + intros phi; simpl.
      apply fol_equiv_ext; f_equal.
      apply vec_pos_ext; intros p.
      rewrite vec_pos_map; apply Hw; auto.
  Qed.

  Fact fol_def_True : fol_definable (fun _ => True).
  Proof. exists (⊥⤑⊥); intros; simpl; msplit 2; try red; simpl; tauto. Qed.
 
  Fact fol_def_False : fol_definable (fun _ => False).
  Proof. exists ⊥; intros; simpl; msplit 2; try red; simpl; tauto. Qed.

  Fact fol_def_equiv R T : 
          (forall φ, R φ <-> T φ) -> fol_definable R -> fol_definable T.
  Proof. 
    intros H (A & H1 & H2 & H3); exists A; msplit 2; auto; intro; rewrite <- H; auto. 
  Qed.

  Fact fol_def_conj R T : 
         fol_definable R -> fol_definable T -> fol_definable (fun φ => R φ /\ T φ).
  Proof.
    intros (A & H1 & H2 & H3) (B & HH4 & H5 & H6); exists (fol_bin fol_conj A B); msplit 2.
    1,2: simpl; intro; rewrite in_app_iff; intros []; auto.
    intro; simpl; rewrite H3, H6; tauto.
  Qed.

  Fact fol_def_disj R T : 
         fol_definable R -> fol_definable T -> fol_definable (fun φ => R φ \/ T φ).
  Proof.
    intros (A & H1 & H2 & H3) (B & HH4 & H5 & H6); exists (fol_bin fol_disj A B); msplit 2.
    1,2: simpl; intro; rewrite in_app_iff; intros []; auto.
    intro; simpl; rewrite H3, H6; tauto.
  Qed.

  Fact fol_def_imp R T : 
         fol_definable R -> fol_definable T -> fol_definable (fun φ => R φ -> T φ).
  Proof.
    intros (A & H1 & H2 & H3) (B & HH4 & H5 & H6); exists (fol_bin fol_imp A B); msplit 2.
    1,2: simpl; intro; rewrite in_app_iff; intros []; auto.
    intro; simpl; rewrite H3, H6; tauto.
  Qed.

  Fact fol_def_fa (R : X -> (nat -> X) -> Prop) :
          fol_definable (fun φ => R (φ 0) (fun n => φ (S n)))
       -> fol_definable (fun φ => forall x, R x φ).
  Proof.
    intros (A & H1 & H2 & H3); exists (fol_quant fol_fa A); msplit 2; auto.
    intro; simpl; apply forall_equiv.
    intro; rewrite H3; simpl; tauto.
  Qed.

  Fact fol_def_ex (R : X -> (nat -> X) -> Prop) :
          fol_definable (fun φ => R (φ 0) (fun n => φ (S n)))
       -> fol_definable (fun φ => exists x, R x φ).
  Proof.
    intros (A & H1 & H2 & H3); exists (fol_quant fol_ex A); msplit 2; auto.
    intro; simpl; apply exists_equiv.
    intro; rewrite H3; simpl; tauto.
  Qed.

  Fact fol_def_list_fa K l (R : K -> (nat -> X) -> Prop) :
           (forall k, In k l -> fol_definable (R k))
        -> fol_definable (fun φ => forall k, In k l -> R k φ).
  Proof.
    intros H.
    set (f := fun k Hk => proj1_sig (H k Hk)).
    exists (fol_lconj (list_in_map l f)); msplit 2. 
    + unfold fol_lconj; rewrite fol_syms_bigop.
      intros s; simpl; rewrite <- app_nil_end.
      rewrite in_flat_map.
      intros (A & H1 & H2).
      apply In_list_in_map_inv in H1.
      destruct H1 as (k & Hk & ->).
      revert H2; apply (proj2_sig (H k Hk)); auto.
    + unfold fol_lconj; rewrite fol_rels_bigop.
      intros s; simpl; rewrite <- app_nil_end.
      rewrite in_flat_map.
      intros (A & H1 & H2).
      apply In_list_in_map_inv in H1.
      destruct H1 as (k & Hk & ->).
      revert H2; apply (proj2_sig (H k Hk)); auto.
    + intros phi.
      rewrite fol_sem_big_conj; split.
      * intros H1 k Hk; apply (proj2_sig (H k Hk)), H1.
        change (In (f k Hk) (list_in_map l f)). 
        apply In_list_in_map.
      * intros H1 A H2.
        apply In_list_in_map_inv in H2.
        destruct H2 as (k & Hk & ->).
        apply (proj2_sig (H k Hk)); auto.
  Qed.

  Fact fol_def_list_ex K l (R : K -> (nat -> X) -> Prop) :
           (forall k, In k l -> fol_definable (R k))
        -> fol_definable (fun φ => exists k, In k l /\ R k φ).
  Proof.
    intros H.
    set (f := fun k Hk => proj1_sig (H k Hk)).
    exists (fol_ldisj (list_in_map l f)); msplit 2. 
    + unfold fol_ldisj; rewrite fol_syms_bigop.
      intros s; simpl; rewrite <- app_nil_end.
      rewrite in_flat_map.
      intros (A & H1 & H2).
      apply In_list_in_map_inv in H1.
      destruct H1 as (k & Hk & ->).
      revert H2; apply (proj2_sig (H k Hk)); auto.
    + unfold fol_ldisj; rewrite fol_rels_bigop.
      intros s; simpl; rewrite <- app_nil_end.
      rewrite in_flat_map.
      intros (A & H1 & H2).
      apply In_list_in_map_inv in H1.
      destruct H1 as (k & Hk & ->).
      revert H2; apply (proj2_sig (H k Hk)); auto.
    + intros phi.
      rewrite fol_sem_big_disj; split.
      * intros (A & H1 & HA).
        apply In_list_in_map_inv in H1.
        destruct H1 as (k & Hk & ->).
        exists k; split; auto.
        apply (proj2_sig (H k Hk)); auto.
      * intros (k & Hk & H1).
        exists (f k Hk); split.
        - apply In_list_in_map.
        - apply (proj2_sig (H k Hk)); auto.
  Qed.

  Fact fol_def_ext R : fol_definable R -> forall φ ψ, (forall n, φ n = ψ n) -> R φ <-> R ψ.
  Proof.
    intros (A & _ & _ & HA) phi psi H.
    rewrite <- HA, <- HA; apply fol_sem_ext.
    intros; auto.
  Qed.

  Fact fol_def_subst (R : (nat -> X) -> Prop) (f : nat -> (nat -> X) -> X) :
          (forall n, fot_definable (f n))
       -> fol_definable R
       -> fol_definable (fun φ => R (fun n => f n φ)).
  Proof.
    intros H1 H2. 
    generalize (fol_def_ext H2); intros H3.
    destruct H2 as (A & G1 & G2 & HA).
    set (rho := fun n => proj1_sig (H1 n)).
    exists (fol_subst rho A); msplit 2. 
    + red; apply Forall_forall; apply fol_syms_subst.
      * intros n Hn; rewrite Forall_forall.
        intro; apply (fun n => proj2_sig (H1 n)).
      * apply Forall_forall, G1.
    + rewrite fol_rels_subst; auto.
    + intros phi.
      rewrite fol_sem_subst, HA.
      apply H3; intro; unfold rho; rew fot.
      apply (fun n => proj2_sig (H1 n)).
  Qed.

End fo_definability.

Create HintDb fol_def_db.

Hint Resolve fot_def_proj fot_def_comp fol_def_True fol_def_False : fol_def_db.

Tactic Notation "fol" "def" := 
   repeat ((  apply fol_def_conj 
           || apply fol_def_disj 
           || apply fol_def_imp 
           || apply fol_def_ex
           || apply fol_def_fa
           || (apply fol_def_atom; intro)
           || apply fol_def_subst); auto with fol_def_db); auto with fol_def_db.

Section extra.

  Variable (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
           (X : Type) (M : fo_model Σ X).

  Fact fol_def_iff R T : 
         fol_definable ls lr M R 
      -> fol_definable ls lr M T 
      -> fol_definable ls lr M (fun φ => R φ <-> T φ).
  Proof.
    intros; fol def.
  Qed.

  Fact fol_def_subst2 R t1 t2 : 
           fol_definable ls lr M (fun φ => R (φ 0) (φ 1))
        -> fot_definable ls M t1
        -> fot_definable ls M t2
        -> fol_definable ls lr M (fun φ => R (t1 φ) (t2 φ)).
  Proof.
    intros H1 H2 H3.
    set (f n := match n with
        | 0 => t1 
        | 1 => t2
        | _ => fun φ => φ 0
      end).
    change (fol_definable ls lr M (fun φ => R (f 0 φ) (f 1 φ))). 
    apply fol_def_subst with (2 := H1) (f := f).
    intros [ | [ | n ] ]; simpl; fol def.
  Qed.

  Let env_vec (φ : nat -> X) n := vec_set_pos (fun p => φ (@pos2nat n p)).
  Let env_env (φ : nat -> X) n k := φ (n+k).

  Fact fol_def_vec_fa n (R : vec X n -> (nat -> X) -> Prop) :
           (fol_definable ls lr M (fun φ => R (env_vec φ n) (env_env φ n)))
         -> fol_definable ls lr M (fun φ => forall v, R v φ).
  Proof.
    revert R; induction n as [ | n IHn ]; intros R HR.
    + revert HR; apply fol_def_equiv; intros phi; simpl.
      split; auto; intros ? v; vec nil v; auto.
    + set (T φ := forall v x, R (x##v) φ).
      apply fol_def_equiv with (R := T).
      * intros phi; unfold T; split.
        - intros H v; vec split v with x; auto.
        - intros H ? ?; apply (H (_##_)).
      * unfold T; apply IHn, fol_def_fa, HR.
  Qed.

  Fact fol_def_finite_fa I (R : I -> (nat -> X) -> Prop) :
            finite_t I
         -> (forall i, fol_definable ls lr M (R i))
         -> fol_definable ls lr M (fun φ => forall i : I, R i φ).
  Proof.
    intros (l & Hl) H.
    apply fol_def_equiv with (R := fun φ => forall i, In i l -> R i φ).
    + intros phi; apply forall_equiv; intro; split; auto.
    + apply fol_def_list_fa; auto.
  Qed.
     
End extra.



