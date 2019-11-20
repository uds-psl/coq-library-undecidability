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

Check eq_rect.

Section signature_transport.

  (** To signatures in computable one-to-one correspondance *)

  Variable (Σ Σ' : fo_signature)
           (i_t : syms Σ -> syms Σ') (j_t : syms Σ' -> syms Σ) 
           (i_t_ar : forall s, ar_syms Σ' (i_t s) = ar_syms Σ s)
           (ij_t : forall s, i_t (j_t s) = s) (ji_t : forall s, j_t (i_t s) = s)
           (i_r : rels Σ -> rels Σ') (j_r : rels Σ' -> rels Σ)
           (i_r_ar : forall s, ar_rels Σ' (i_r s) = ar_rels Σ s)
           (ij_r : forall s, i_r (j_r s) = s) (ji_r : forall s, j_r (i_r s) = s).

  Definition fo_term_map_sig X : fo_term X (ar_syms Σ) -> fo_term X (ar_syms Σ').
  Proof.
    apply fo_term_recursion.
    + intros n; exact (in_var n).
    + intros s _ w.
      rewrite <- (i_t_ar s) in w.
      exact (in_fot (i_t s) w).
  Defined.

  Fact fo_term_map_sig_fix0 X x : @fo_term_map_sig X (in_var x) = in_var x.
  Proof. apply fo_term_recursion_fix_0. Qed.

  (** This one needs transport *)

  Fact fo_term_map_sig_fix1 X s v : @fo_term_map_sig X (in_fot s v) 
                                  = in_fot (i_t s) (eq_rect_r _ (vec_map (@fo_term_map_sig X) v) (i_t_ar s)).
  Proof.
    unfold fo_term_map_sig at 1; rewrite fo_term_recursion_fix_1; auto.
  Qed.

  Opaque fo_term_map_sig.

  (** One also needs transport here *)

  Fixpoint fol_map_sig (A : fol_form Σ) : fol_form Σ'.
  Proof.
    refine (match A with
      | ⊥              => ⊥
      | fol_atom _ p v => fol_atom _ (i_r p) _
      | fol_bin c A B => fol_bin c (fol_map_sig A) (fol_map_sig B)
      | fol_quant q A => fol_quant q (fol_map_sig A)
    end).
    rewrite i_r_ar.
    apply (vec_map (@fo_term_map_sig _) v).
  Defined.

  Variable (X : Type) (M : fo_model Σ X).

  Let M' : fo_model Σ' X.
  Proof.
    exists.
    + intros s.
      rewrite <- (ij_t s), i_t_ar.
      apply (fom_syms M (j_t s)).
    + intros r.
      rewrite <- (ij_r r), i_r_ar.
      apply (fom_rels M (j_r r)).
  Defined.

  Let simul_term (φ : nat -> X) t : fo_term_sem (fom_syms M) φ t = fo_term_sem (fom_syms M') φ (fo_term_map_sig t).
  Proof.
    induction t as [ n | s v IHv ].
    + rewrite fo_term_map_sig_fix0; rew fot; auto.
    + rewrite fo_term_map_sig_fix1; rew fot.
      unfold M'; simpl.
      SearchAbout [ eq_rect eq_rect_r ].
      admit.
  Admitted.

  Let simul_form A : forall φ, fol_sem M φ A <-> fol_sem M' φ (fol_map_sig A).
  Proof.
    induction A as [ | s v | b A HA B HB | q A HA ]; intros phi; try (simpl; tauto).
    + unfold fol_map_sig.
      admit.
    + apply fol_bin_sem_ext; auto.
    + apply fol_quant_sem_ext; auto.
  Admitted.

  Theorem fo_signature_transport : { N | forall φ A, fol_sem M φ A <-> fol_sem N φ (fol_map_sig A) }.
  Proof. exists M'; intros; apply simul_form. Qed.

End signature_transport.

Check fo_signature_transport.

