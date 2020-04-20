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
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms.

Set Implicit Arguments.

(** * The syntax and semantics of FO logic *)

Notation ø := vec_nil.

Opaque fo_term_subst fo_term_map fo_term_sem.

(* Terms are just variables in Σrel *)

Definition Σrel_var k : fol_term (Σrel k) -> nat.
Proof. intros [ n | [] ]; exact n. Defined.

(** Unscoped (nat) DeBruijn syntax for FOL formulas *)

Inductive fol_form (Σ : fo_signature) : Type :=
  | fol_false : fol_form Σ
  | fol_atom  : forall p, vec (fol_term Σ) (ar_rels Σ p) -> fol_form Σ 
  | fol_bin   : fol_bop -> fol_form Σ -> fol_form Σ -> fol_form Σ 
  | fol_quant : fol_qop -> fol_form Σ -> fol_form Σ.

Infix "⤑" := (fol_bin fol_imp) (at level 62, right associativity).
Infix "⟑" := (fol_bin fol_conj) (at level 60, right associativity).
Infix "⟇" := (fol_bin fol_disj) (at level 61, right associativity).
Notation "∀ f" := (fol_quant fol_fa f) (at level 64, right associativity).
Notation "∃ f" := (fol_quant fol_ex f) (at level 64, right associativity).
Notation "x ↔ y" := ((x⤑y)⟑(y⤑x)) (at level 63, no associativity).

Notation "£" := (in_var : nat -> fol_term _).
Notation "⊥" := (fol_false _).

Section fol_subst.

  Variable (Σ : fo_signature).

  Notation 𝕋 := (fol_term Σ).
  Notation 𝔽 := (fol_form Σ).

  Implicit Type A : 𝔽.

  Fixpoint fol_height A :=
    match A with
      | ⊥             => 1
      | fol_atom p v  => 1 
      | fol_bin c A B => 1 + max (fol_height A) (fol_height B)
      | fol_quant q A => 1 + fol_height A
    end.

  Fixpoint fol_vars A :=
    match A with
      | ⊥             => nil
      | fol_atom p v  => flat_map fo_term_vars (vec_list v)
      | fol_bin c A B => fol_vars A ++ fol_vars B
      | fol_quant q A => flat_map (fun n => match n with 0 => nil | S n => n::nil end)
                           (fol_vars A) 
    end.

  Fact fol_vars_bin b A B : fol_vars (fol_bin b A B) = fol_vars A ++ fol_vars B.
  Proof. trivial. Qed.

  Fact fol_vars_quant q A : fol_vars (fol_quant q A) 
                         = flat_map (fun n => match n with 0 => nil | S n => n::nil end) (fol_vars A).
  Proof. trivial. Qed.

  Definition fol_vars_max A := lmax (fol_vars A).

  Fact fol_vars_max_spec A n : In n (fol_vars A) -> n <= fol_vars_max A.
  Proof. apply lmax_prop. Qed.

  Fixpoint fol_syms (A : 𝔽) :=
    match A with
      | ⊥              => nil
      | fol_atom p v   => flat_map fo_term_syms (vec_list v)
      | fol_bin c A B  => fol_syms A ++ fol_syms B
      | fol_quant q A  => fol_syms A 
    end.

  Fact fol_syms_bin b A B : fol_syms (fol_bin b A B) = fol_syms A ++ fol_syms B.
  Proof. trivial. Qed.

  Fact fol_syms_quant q A : fol_syms (fol_quant q A) = fol_syms A.
  Proof. trivial. Qed.

  Fixpoint fol_rels (A : 𝔽) :=
    match A with
      | ⊥              => nil
      | fol_atom p v   => p::nil
      | fol_bin c A B  => fol_rels A ++ fol_rels B
      | fol_quant q A  => fol_rels A 
    end.

  Fact fol_rels_bin b A B : fol_rels (fol_bin b A B) = fol_rels A ++ fol_rels B.
  Proof. trivial. Qed.

  Fact fol_rels_quant q A : fol_rels (fol_quant q A) = fol_rels A.
  Proof. trivial. Qed.

  Fixpoint fol_subst σ (A : 𝔽) :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ v   => fol_atom _ (vec_map (fo_term_subst σ) v)
      | fol_bin c A B => fol_bin c (A⦃σ⦄) (B⦃σ⦄)
      | fol_quant q A => fol_quant q (A⦃⇡σ⦄) 
    end
  where "A ⦃ σ ⦄" := (fol_subst σ A).

  Fact fol_subst_ext σ ρ A : 
         (forall n, In n (fol_vars A) -> σ n = ρ n) 
       -> A⦃σ⦄ = A⦃ρ⦄.
  Proof.
    intros Hfg; revert A σ ρ Hfg. 
    induction A as [ | p v | c A IHA B IHB | q A IHA ]; intros f g Hfg; simpl; f_equal; auto.
    + apply vec_map_ext; intros t Ht. 
      apply fo_term_subst_ext; intros n Hn.
      apply Hfg, in_flat_map; exists t; split; auto.
      apply in_vec_list; auto.
    + apply IHA; intros n Hn; apply Hfg, in_or_app; auto.
    + apply IHB; intros n Hn; apply Hfg, in_or_app; auto.
    + apply IHA; intros [ | n ] Hn; simpl; auto; rew fot.
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

  Fact fol_vars_bigop c l A : fol_vars (fol_bigop c A l) = flat_map fol_vars l++fol_vars A.
  Proof.
    induction l; simpl; auto.
    rewrite app_ass; f_equal; auto.
  Qed.

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

Notation fol_lconj := (@fol_bigop _ fol_conj (⊥⤑⊥)).
Notation fol_ldisj := (@fol_bigop _ fol_disj ⊥).

Section fol_semantics.

  Variable (Σ : fo_signature) 
           (X : Type) (M : fo_model Σ X).

  Implicit Type φ : nat -> X.

  Notation 𝕋 := (fol_term Σ).
  Notation 𝔽 := (fol_form Σ).

  Notation "⟦ t ⟧" := (fun φ => fo_term_sem M φ t).

  Fixpoint fol_sem φ A : Prop :=
    match A with
      | ⊥              => False
      | fol_atom _ v   => fom_rels M _ (vec_map (fun t => ⟦t⟧ φ) v)
      | fol_bin b A B  => fol_bin_sem b (⟪A⟫ φ) (⟪B⟫ φ) 
      | fol_quant q A  => fol_quant_sem q (fun x => ⟪A⟫ x·φ)
    end
  where "⟪ A ⟫" := (fun φ => fol_sem φ A).

  Fact fol_sem_bin_fix φ b A B : fol_sem φ (fol_bin b A B) = fol_bin_sem b (⟪A⟫ φ) (⟪B⟫ φ).
  Proof. reflexivity. Qed.

  Fact fol_sem_quant_fix φ q A : fol_sem φ (fol_quant q A) = fol_quant_sem q (fun x => ⟪A⟫ x·φ).
  Proof. reflexivity. Qed.

  (** Semantics depends only on occuring variables *)

  Fact fol_sem_ext φ ψ A : (forall n, In n (fol_vars A) -> φ n = ψ n) -> ⟪A⟫ φ <-> ⟪A⟫ ψ.
  Proof.
    intros H; revert A φ ψ H.
    induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros phi psy H; try tauto.
    + apply fol_equiv_ext; f_equal.
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

  Section decidable.

    (** REMARK: not requiring the fom_rels M s relation to be decidable
        would allow hiding uncomputability inside the model which
        would be kind of cheating. The semantic relation should be
        decidable, only the (finite) satisfiability relation should 
        be undec *)

    (** For the semantics relation to be decidable over a finite domain,
        it is necessary and SUFFICIENT that the sem_pred relation is decidable
        or equivalently, each predicate is interpreted as a map: vec X _ -> bool *)

    Variable (M_fin : finite_t X).
    Variable (rels_dec : fo_model_dec M).

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

  (** Semantics commutes with substitutions ... good *)

  Theorem fol_sem_subst φ σ A : ⟪ A⦃σ⦄ ⟫ φ <-> ⟪A⟫ (fun n => ⟦σ n⟧ φ).
  Proof.
    revert φ σ; induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros phi f; try tauto.
    + apply fol_equiv_ext; f_equal.
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

  Definition fol_lift t n : 𝕋 := match n with 0 => t | S n => £n end.

  Corollary fol_sem_lift φ t A : ⟪ A⦃fol_lift t⦄ ⟫ φ <-> ⟪A⟫ (⟦t⟧ φ)·φ.
  Proof.
    rewrite fol_sem_subst.
    apply fol_sem_ext; intros [ | n ] _; simpl; rew fot; auto.
  Qed.

  (** Bigops, ie finitary conjunction and disjunction *)

  Fact fol_sem_lconj lf φ : ⟪fol_lconj lf⟫ φ <-> forall f, In f lf -> ⟪ f ⟫ φ.
  Proof.
    induction lf as [ | f lf IHlf ]; simpl.
    + split; tauto.
    + rewrite IHlf.
      split.
      * intros [] ? [ -> | ]; auto.
      * intros H; split; intros; apply H; auto.
  Qed.

  Fact fol_sem_lconj_app l m φ : 
            ⟪ fol_lconj (l++m) ⟫ φ 
        <-> ⟪ fol_lconj l ⟫ φ 
         /\ ⟪ fol_lconj m ⟫ φ.
  Proof.
    do 3 rewrite fol_sem_lconj; split.
    + intros H; split; intros; apply H, in_app_iff; firstorder.
    + intros (H1 & H2) f; rewrite in_app_iff; firstorder.
  Qed.

  Fact fol_sem_ldisj lf φ : ⟪fol_ldisj lf⟫ φ <-> exists f, In f lf /\ ⟪ f ⟫ φ.
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

  Fact fol_sem_ldisj_app l m φ : 
            ⟪ fol_ldisj (l++m) ⟫ φ 
        <-> ⟪ fol_ldisj l ⟫ φ 
         \/ ⟪ fol_ldisj m ⟫ φ.
  Proof.
    do 3 rewrite fol_sem_ldisj; split.
    + intros (f & H1 & H2); revert H1; rewrite in_app_iff; firstorder.
    + intros [ (? & ? & ?) | (? & ? & ?) ]; firstorder.
  Qed.

  Definition fol_vec_fa n (A : vec 𝔽 n) := fol_lconj (vec_list A).

  Fact fol_vars_vec_fa n A : fol_vars (@fol_vec_fa n A) = flat_map (@fol_vars _) (vec_list A).
  Proof.
    unfold fol_vec_fa; rewrite fol_vars_bigop; simpl.
    rewrite app_nil_end; auto. 
  Qed.

  Fact fol_syms_vec_fa n A : fol_syms (@fol_vec_fa n A) = flat_map (@fol_syms _) (vec_list A).
  Proof.
    unfold fol_vec_fa; rewrite fol_syms_bigop; simpl.
    rewrite app_nil_end; auto. 
  Qed.

  Fact fol_rels_vec_fa n A : fol_rels (@fol_vec_fa n A) = flat_map (@fol_rels _) (vec_list A).
  Proof.
    unfold fol_vec_fa; rewrite fol_rels_bigop; simpl.
    rewrite app_nil_end; auto. 
  Qed.
 
  Fact fol_sem_vec_fa n A φ : ⟪ @fol_vec_fa n A ⟫ φ <-> forall p, ⟪ vec_pos A p ⟫ φ.
  Proof.
    unfold fol_vec_fa; rewrite fol_sem_lconj; split.
    + intros H p; apply H, in_vec_list, in_vec_pos.
    + intros H f Hf.
      apply vec_list_inv in Hf.
      destruct Hf as (p & ->); auto.
  Qed.

  (** [x1;...;xn] · φ := x1 · x2 ... · xn · φ *)

  Fixpoint env_vlift φ n (v : vec X n) :=
    match v with
      | ø    => φ
      | x##v => x·(env_vlift φ v)
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
    revert φ k; induction v as [ | x n v IHv ]; intros phi k; simpl; auto.
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

End fol_semantics.

(*
Notation fol_sem_big_conj := fol_sem_lconj.
Notation fol_sem_big_disj := fol_sem_ldisj.
*)

Definition fot_vec_env Σ n p : 
        { w : vec (fo_term (ar_syms Σ)) n | (forall X (M : fo_model Σ X) v φ q x, 
             fo_term_sem M x·(env_vlift φ v) (vec_pos w q) 
           = vec_pos (vec_change v p x) q)
         /\ forall q, fo_term_syms (vec_pos w q) = nil }.
Proof.
  exists (vec_change (vec_set_pos (fun q => £(S (pos2nat q)))) p (£0)); split.
  * intros X M v phi q x;rew fot; rew vec; rew fot.
    destruct (pos_eq_dec p q) as [ H | H ].
    + rewrite !vec_change_eq; auto.
    + rewrite !vec_change_neq; auto; rew vec; rew fot; simpl.
      rewrite env_vlift_fix0; auto.
  * intros q; destruct (pos_eq_dec p q) as [ H | H ].
    + rewrite !vec_change_eq; auto.
    + rewrite !vec_change_neq; auto; rew vec.
Qed.

Section fo_model_simulation.

  (** We state a general simulation result for models on a given 
      formula build on a bounded list of symbols. The statement
      is so general that the proof is just obvious ;-) *)

  Variables  (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
             (X : Type) (M : fo_model Σ X)
             (Y : Type) (N : fo_model Σ Y).

  (** We assume that ⋈ is a simulation, ie a congruence for all operators in ls
      and all relations in lr *)

  Record fo_simulation := Mk_fo_simulation {
    fos_simul :> X -> Y -> Prop;
    fos_syms  : forall s v w, In s ls 
                          -> (forall p, fos_simul (vec_pos v p) (vec_pos w p))
                          -> fos_simul (fom_syms M s v) (fom_syms N s w);
    fos_rels  : forall s v w, In s lr 
                          -> (forall p, fos_simul (vec_pos v p) (vec_pos w p))
                          -> fom_rels M s v <-> fom_rels N s w;
    fos_total : forall x, exists y, fos_simul x y;
    fos_surj  : forall y, exists x, fos_simul x y;
  }.

  Record fo_projection := Mk_fo_projection {
    fop_surj :> X -> Y; 
    fop_inj  : Y -> X;
    fop_eq   : forall x, fop_surj (fop_inj x) = x;
    fop_syms : forall s v, In s ls -> fop_surj (fom_syms M s v) = fom_syms N s (vec_map fop_surj v);
    fop_rels : forall s v, In s lr -> fom_rels M s v <-> fom_rels N s (vec_map fop_surj v);
  }.

  Fact fo_proj_simul : fo_projection -> fo_simulation.
  Proof.
    intros [ i j E Hs Hr ].
    exists (fun x y => i x = y); auto.
    + intros s v w H1 H2; rewrite Hs; auto.
      f_equal; apply vec_pos_ext; intro; rew vec.
    + intros s v w H1 H2; rewrite Hr; auto.
      apply fol_equiv_ext; f_equal.
      apply vec_pos_ext; intro; rew vec.
    + intros x; exists (i x); auto.
    + intros y; exists (j y); auto.
  Defined.

  Variable R : fo_simulation.

  Infix "⋈" := R (at level 70, no associativity).
  
  Notation "⟦ t ⟧" := (fun φ => fo_term_sem M φ t).
  Notation "⟦ t ⟧'" := (fun φ => fo_term_sem N φ t) (at level 1, format "⟦ t ⟧'").

  Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
  Notation "⟪ A ⟫'" := (fun φ => fol_sem N φ A) (at level 1, format "⟪ A ⟫'").

  (** The simulation lifts from variables to terms *)

  Let fo_term_simulation t φ ψ :
           (forall n : nat, In n (fo_term_vars t) -> φ n ⋈ ψ n) 
        -> incl (fo_term_syms t) ls
        -> ⟦t⟧ φ ⋈ ⟦t⟧' ψ.
  Proof.
    revert φ ψ.
    induction t as [ k | s v IH ]; 
      intros phi psi Hv Hls; rew fot; auto.
    + apply Hv; simpl; auto.
    + apply fos_syms.
      * apply Hls; simpl; auto.
      * intros p; do 2 rewrite vec_pos_map.
        apply IH; auto.
        - intros n Hn; apply Hv; rew fot.
          apply in_flat_map.
          exists (vec_pos v p); split; auto.
          apply in_vec_list, in_vec_pos.
        - apply incl_tran with (2 := Hls).
          intros s' Hs'; rew fot.
          right; apply in_flat_map.
          exists (vec_pos v p); split; auto.
          apply in_vec_list, in_vec_pos.
  Qed.

  (** We assume the simulation to be total and surjective *)

  Theorem fo_model_simulation A φ ψ :
           incl (fol_syms A) ls
        -> incl (fol_rels A) lr
        -> (forall n : nat, In n (fol_vars A) -> φ n ⋈ ψ n) 
        -> ⟪A⟫ φ <-> ⟪A⟫' ψ.
  Proof.
    revert φ ψ.
    induction A as [ | r v | b A HA B HB | q A HA ]; intros phi psi Hs1 Hr1 Hp; simpl; try tauto.
    + apply (fos_rels R).
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
      3,6: intros; apply Hp; simpl; apply in_or_app; auto.
      1,3: apply incl_tran with (2 := Hs1); intros ? ?; apply in_or_app; auto.
      1,2: apply incl_tran with (2 := Hr1); intros ? ?; apply in_or_app; auto.
    + destruct q; simpl; split.
      1: intros (x & Hx); destruct (fos_total R x) as (y & Hy); exists y; revert Hx; apply HA; eauto.
      2: intros (y & Hy); destruct (fos_surj R y) as (x & Hx); exists x; revert Hy; apply HA; eauto.
      3: intros H y; destruct (fos_surj R y) as (x & Hx); generalize (H x); apply HA; eauto.
      4: intros H x; destruct (fos_total R x) as (y & Hy); generalize (H y); apply HA; eauto.
      all: intros []; simpl; auto; intros; apply Hp, in_flat_map; exists (S n); simpl; auto.
  Qed.

End fo_model_simulation.

Theorem fo_model_projection Σ ls lr X M Y N (p : @fo_projection Σ ls lr X M Y N) A φ ψ : 
           (forall n, In n (fol_vars A) -> p (φ n) = ψ n)
        -> incl (fol_syms A) ls 
        -> incl (fol_rels A) lr
        -> fol_sem M φ A <-> fol_sem N ψ A.
Proof.
  intros H1 H2 H3.
  apply fo_model_simulation with (R := fo_proj_simul p); auto.
  destruct p; simpl; auto.
Qed.

Section fo_model_projection.

  (** We specialize the previous simulation result on simulation
      obtained as surjective projections *)

  Variable (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
           (X : Type) (M : fo_model Σ X) (φ : nat -> X) 
           (Y : Type) (N : fo_model Σ Y) (ψ : nat -> Y)
           (i : X -> Y) (j : Y -> X) (E : forall x, i (j x) = x)
           (Hs : forall s v, In s ls -> i (fom_syms M s v) = fom_syms N s (vec_map i v))
           (Hr : forall s v, In s lr -> fom_rels M s v <-> fom_rels N s (vec_map i v)).
  
  Let p : fo_projection ls lr M N.
  Proof. exists i j; auto. Defined.

  Theorem fo_model_projection' A : 
           (forall n, In n (fol_vars A) -> i (φ n) = ψ n)
        -> incl (fol_syms A) ls 
        -> incl (fol_rels A) lr
        -> fol_sem M φ A <-> fol_sem N ψ A.
  Proof. apply fo_model_projection with (p := p). Qed.

End fo_model_projection.

Section fo_model_nosyms.

  Variable (Σ : fo_signature)
           (X : Type) (M M' : fo_model Σ X) (φ : nat -> X)
           (A : fol_form Σ)
           (HA : fol_syms A = nil)
           (H : forall r v, In r (fol_rels A) -> fom_rels M r v <-> fom_rels M' r v).

  Theorem fo_model_nosyms : fol_sem M φ A <-> fol_sem M' φ A.
  Proof.
    apply fo_model_projection' with (ls := nil) (lr := fol_rels A) (i := fun x => x) (j := fun x => x); auto.
    + intros ? ? [].
    + intros; rewrite H; auto.
      apply fol_equiv_ext; f_equal.
      apply vec_pos_ext; intro; rew vec.
    + rewrite HA; apply incl_refl.
    + apply incl_refl.
  Qed.

End fo_model_nosyms.

