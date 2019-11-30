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
  Require Import notations fol_ops utils fo_terms fo_logic.

Set Implicit Arguments.

Notation ø := vec_nil.

Opaque fo_term_subst fo_term_map fo_term_sem.

Section fo_definability.

  Variable (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
         (*  (X : Type) (M : fo_model Σ X) *).

  Definition fot_definable (f : forall X, fo_model Σ X -> (nat -> X) -> X) := 
       { t |  incl (fo_term_syms t) ls /\ forall X (M : fo_model Σ X) φ, fo_term_sem (fom_syms M) φ t = f X M φ }.

  Definition fol_definable (R : forall X, fo_model Σ X -> (nat -> X) -> Prop) :=
       { A | incl (fol_syms A) ls 
          /\ incl (fol_rels A) lr 
          /\ forall X (M : fo_model Σ X) φ, fol_sem M φ A <-> R X M φ }.

  (** A FOL definable predicate is always extensional *)

  Fact fot_def_ext t : fot_definable t -> forall X (M : fo_model Σ X) φ ψ, (forall n, φ n = ψ n) -> t X M φ = t X M ψ.
  Proof.
    intros (k & _ & Hk) X M phi psi H.
    rewrite <- (Hk _ M), <- (Hk _ M); apply fo_term_sem_ext; auto.
  Qed.

  Fact fol_def_ext R : fol_definable R -> forall X (M : fo_model Σ X) φ ψ, (forall n, φ n = ψ n) -> R X M φ <-> R X M ψ.
  Proof.
    intros (A & _ & _ & HA) X M phi psi H.
    rewrite <- (HA _ M), <- (HA _ M); apply fol_sem_ext.
    intros; auto.
  Qed.

  (** We derive closure properties *)

  Fact fot_def_proj n : fot_definable (fun _ _ φ => φ n).
  Proof. exists (£ n); intros; split; rew fot; auto; intros _ []. Qed.

  Fact fot_def_map (f : nat -> nat) t :
           fot_definable t -> fot_definable (fun X M φ => t X M (fun n => φ (f n))).
  Proof.
    intros H; generalize (fot_def_ext H); revert H.
    intros (k & H1 & H2) H3.
    exists (fo_term_map f k); split.
    + rewrite fo_term_syms_map; auto.
    + intros X M phi; rewrite <- fo_term_subst_map; rew fot.
      rewrite (H2 _ M); apply H3; auto.
  Qed.
 
  Fact fot_def_comp s v : 
        In s ls
      -> (forall p, fot_definable (fun X M φ => vec_pos (v X M φ) p))
      -> fot_definable (fun X M φ => fom_syms M s (v X M φ)).
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
    + intros X M phi; rew fot; f_equal.
      apply vec_pos_ext; intros p.
      rewrite vec_pos_map.
      apply Hw; auto.
  Qed.

  Fact fot_def_equiv f g : 
         (forall X M φ, f X M φ = g X M φ) -> fot_definable f -> fot_definable g.
  Proof.
    intros E (t & H1 & H2); exists t; split; auto; intros X M phi; rewrite (H2 _ M); auto.
  Qed.

  Fact fol_def_atom r v :
         In r lr
      -> (forall p, fot_definable (fun X M φ => vec_pos (v X M φ) p))
      -> fol_definable (fun X M φ => fom_rels M r (v X M φ)).
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
    + intros X M phi; simpl.
      apply fol_equiv_ext; f_equal.
      apply vec_pos_ext; intros p.
      rewrite vec_pos_map; apply Hw; auto.
  Qed.

  Fact fol_def_True : fol_definable (fun _ _ _ => True).
  Proof. exists (⊥⤑⊥); intros; simpl; msplit 2; try red; simpl; tauto. Qed.
 
  Fact fol_def_False : fol_definable (fun _ _ _ => False).
  Proof. exists ⊥; intros; simpl; msplit 2; try red; simpl; tauto. Qed.

  Fact fol_def_equiv R T : 
          (forall X M φ, R X M φ <-> T X M φ) -> fol_definable R -> fol_definable T.
  Proof. 
    intros H (A & H1 & H2 & H3); exists A; msplit 2; auto; intros X M phi; rewrite <- (H _ M); auto. 
  Qed.

  Fact fol_def_conj R T : 
         fol_definable R -> fol_definable T -> fol_definable (fun X M φ => R X M φ /\ T X M φ).
  Proof.
    intros (A & H1 & H2 & H3) (B & HH4 & H5 & H6); exists (fol_bin fol_conj A B); msplit 2.
    1,2: simpl; intro; rewrite in_app_iff; intros []; auto.
    intros ? M ?; simpl; rewrite (H3 _ M), (H6 _ M); tauto.
  Qed.

  Fact fol_def_disj R T : 
         fol_definable R -> fol_definable T -> fol_definable (fun X M φ => R X M φ \/ T X M φ).
  Proof.
    intros (A & H1 & H2 & H3) (B & HH4 & H5 & H6); exists (fol_bin fol_disj A B); msplit 2.
    1,2: simpl; intro; rewrite in_app_iff; intros []; auto.
    intros ? M ?; simpl; rewrite (H3 _ M), (H6 _ M); tauto.
  Qed.

  Fact fol_def_imp R T : 
         fol_definable R -> fol_definable T -> fol_definable (fun X M φ => R X M φ -> T X M φ).
  Proof.
    intros (A & H1 & H2 & H3) (B & HH4 & H5 & H6); exists (fol_bin fol_imp A B); msplit 2.
    1,2: simpl; intro; rewrite in_app_iff; intros []; auto.
    intros ? M ?; simpl; rewrite (H3 _ M), (H6 _ M); tauto.
  Qed.

  Fact fol_def_fa (R : forall X, fo_model Σ X -> X -> (nat -> X) -> Prop) :
          fol_definable (fun X M φ => R X M (φ 0) (fun n => φ (S n)))
       -> fol_definable (fun X M φ => forall x, R X M x φ).
  Proof.
    intros (A & H1 & H2 & H3); exists (fol_quant fol_fa A); msplit 2; auto.
    intros X M phi; simpl; apply forall_equiv.
    intro; rewrite H3; simpl; tauto.
  Qed.

  Fact fol_def_ex (R : forall X, fo_model Σ X -> X -> (nat -> X) -> Prop) :
          fol_definable (fun X M φ => R X M (φ 0) (fun n => φ (S n)))
       -> fol_definable (fun X M φ => exists x, R X M x φ).
  Proof.
    intros (A & H1 & H2 & H3); exists (fol_quant fol_ex A); msplit 2; auto.
    intros ? ? ?; simpl; apply exists_equiv.
    intro; rewrite H3; simpl; tauto.
  Qed.

  Fact fol_def_list_fa K l (R : K -> forall X, fo_model Σ X -> (nat -> X) -> Prop) :
           (forall k, In k l -> fol_definable (R k))
        -> fol_definable (fun X M φ => forall k, In k l -> R k X M φ).
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
    + intros X M phi.
      rewrite fol_sem_lconj; split.
      * intros H1 k Hk; apply (proj2_sig (H k Hk)), H1.
        change (In (f k Hk) (list_in_map l f)). 
        apply In_list_in_map.
      * intros H1 A H2.
        apply In_list_in_map_inv in H2.
        destruct H2 as (k & Hk & ->).
        apply (proj2_sig (H k Hk)); auto.
  Qed.

  Fact fol_def_bounded_fa m (R : nat -> forall X, fo_model Σ X -> (nat -> X) -> Prop) :
             (forall n, n < m -> fol_definable (R n))
          -> fol_definable (fun X M φ => forall n, n < m -> R n X M φ).
  Proof.
    intros H.
    apply fol_def_equiv with (R := fun X M φ => forall n, In n (list_an 0 m) -> R n X M φ).
    + intros X M phi; apply forall_equiv; intro; rewrite list_an_spec; simpl; split; try tauto.
      intros H1 ?; apply H1; lia.
    + apply fol_def_list_fa.
      intros n Hn; apply H; revert Hn; rewrite list_an_spec; lia.
  Qed.

  Fact fol_def_list_ex K l (R : K -> forall X, fo_model Σ X -> (nat -> X) -> Prop) :
           (forall k, In k l -> fol_definable (R k))
        -> fol_definable (fun X M φ => exists k, In k l /\ R k X M φ).
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
    + intros X M phi.
      rewrite fol_sem_ldisj; split.
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

  Fact fol_def_subst R (f : nat -> forall X, fo_model Σ X -> (nat -> X) -> X) :
          (forall n, fot_definable (f n))
       -> fol_definable R
       -> fol_definable (fun X M φ => R X M (fun n => f n X M φ)).
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
    + intros X M phi.
      rewrite fol_sem_subst, HA.
      apply H3; intro; unfold rho; rew fot.
      apply (fun n => proj2_sig (H1 n)).
  Qed.

End fo_definability.

Create HintDb fol_def_db.

Hint Resolve fot_def_proj fot_def_map fot_def_comp fol_def_True fol_def_False : fol_def_db.

Tactic Notation "fol" "def" := 
   repeat ((  apply fol_def_conj 
           || apply fol_def_disj 
           || apply fol_def_imp 
           || apply fol_def_ex
           || apply fol_def_fa
           || (apply fol_def_atom; intro)
           || apply fol_def_subst); auto with fol_def_db); auto with fol_def_db.

Section extra.

  Variable (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ)).
         (*  (X : Type) (M : fo_model Σ X). *)

  (** More closure properties *)

  Fact fol_def_iff R T : 
         fol_definable ls lr R 
      -> fol_definable ls lr T 
      -> fol_definable ls lr (fun X M φ => R X M φ <-> T X M φ).
  Proof.
    intros; fol def.
  Qed.

  Fact fol_def_subst1 R t : 
           fol_definable ls lr (fun X M φ => R X M (φ 0))
        -> fot_definable ls t
        -> fol_definable ls lr (fun X M φ => R X M (t X M φ)).
  Proof.
    intros H1 H2.
    set (f n := match n with
        | 0 => t 
        | _ => fun X M φ => φ 0
      end).
    change (fol_definable ls lr (fun X M φ => R X M (f 0 X M φ))). 
    apply fol_def_subst with (2 := H1) (f := f).
    intros [ | ]; simpl; fol def.
  Qed.

  Fact fol_def_subst_R_2 (R : forall X, fo_model Σ X -> (nat -> X) -> X -> X -> Prop) f t1 t2 : 
           fol_definable ls lr (fun X M φ => R X M (fun n => φ (2+n)) (φ 0) (φ 1))
        -> fot_definable ls t1
        -> fot_definable ls t2
        -> fol_definable ls lr (fun X M φ => R X M (fun n => φ (f n)) (t1 X M φ) (t2 X M φ)).
  Proof.
    intros H1 H2 H3.
    set (g n := match n with
        | 0 => t1 
        | 1 => t2
        | S (S n) => fun X M φ => φ (f n)
      end).
    change (fol_definable ls lr (fun X M φ => R X M (fun n => g (2+n) X M φ) (g 0 X M φ) (g 1 X M φ))).
    apply fol_def_subst with (2 := H1) (f := g).
    intros [ | [] ]; simpl; fol def.
  Qed.

  Fact fol_def_dec A : { A } + { ~ A } -> fol_definable ls lr (fun _ _ _ => A).
  Proof.
    intros [ H | H ].
    + apply fol_def_equiv with (R := fun _ _ _ => True); try tauto; fol def.
    + apply fol_def_equiv with (R := fun _ _ _ => False); try tauto; fol def.
  Qed.

  Fact fol_def_subst2 R t1 t2 : 
           fol_definable ls lr (fun X M φ => R X M (φ 0) (φ 1))
        -> fot_definable ls t1
        -> fot_definable ls t2
        -> fol_definable ls lr (fun X M φ => R X M (t1 X M φ) (t2 X M φ)).
  Proof.
    intros H1 H2 H3.
    set (f n := match n with
        | 0 => t1 
        | 1 => t2
        | _ => fun X M φ => φ 0
      end).
    change (fol_definable ls lr (fun X M φ => R X M (f 0 X M φ) (f 1 X M φ))). 
    apply fol_def_subst with (2 := H1) (f := f).
    intros [ | [ | n ] ]; simpl; fol def.
  Qed.

  Fact fol_def_subst3 R t1 t2 t3 : 
           fol_definable ls lr (fun X M φ => R X M (φ 0) (φ 1) (φ 2))
        -> fot_definable ls t1
        -> fot_definable ls t2
        -> fot_definable ls t3
        -> fol_definable ls lr (fun X M φ => R X M (t1 X M φ) (t2 X M φ) (t3 X M φ)).
  Proof.
    intros H1 H2 H3 H4.
    set (f n := match n with
        | 0 => t1 
        | 1 => t2
        | 2 => t3
        | _ => fun X M φ => φ 0
      end).
    change (fol_definable ls lr (fun X M φ => R X M (f 0 X M φ) (f 1 X M φ) (f 2 X M φ))). 
    apply fol_def_subst with (2 := H1) (f := f).
    intros [ | [ | [ | n ] ] ]; simpl; fol def.
  Qed.

  Let env_vec X (φ : nat -> X) n := vec_set_pos (fun p => φ (@pos2nat n p)).
  Let env_env X (φ : nat -> X) n k := φ (n+k).

  Fact fol_def_vec_fa n (R : forall X, fo_model Σ X -> vec X n -> (nat -> X) -> Prop) :
           (fol_definable ls lr (fun X M φ => R X M (env_vec φ n) (env_env φ n)))
         -> fol_definable ls lr (fun X M φ => forall v, R X M v φ).
  Proof.
    revert R; induction n as [ | n IHn ]; intros R HR.
    + revert HR; apply fol_def_equiv; intros phi; simpl.
      split; auto; intros ? v; vec nil v; auto.
    + set (T X M φ := forall v x, R X M (x##v) φ).
      apply fol_def_equiv with (R := T).
      * intros phi; unfold T; split.
        - intros H v; vec split v with x; auto.
        - intros H ? ?; apply (H (_##_)).
      * unfold T; apply IHn, fol_def_fa, HR.
  Qed.

  Fact fol_def_vec_ex n (R : forall X, fo_model Σ X -> vec X n -> (nat -> X) -> Prop) :
           (fol_definable ls lr (fun X M φ => R X M (env_vec φ n) (env_env φ n)))
         -> fol_definable ls lr (fun X M φ => exists v, R X M v φ).
  Proof.
    revert R; induction n as [ | n IHn ]; intros R HR.
    + revert HR; apply fol_def_equiv; intros phi; simpl.
      split.
      * exists vec_nil; auto.
      * intros (v & Hv); revert Hv; vec nil v; auto.
    + set (T X M φ := exists v x, R X M (x##v) φ).
      apply fol_def_equiv with (R := T).
      * intros phi; unfold T; split.
        - intros (v & x & Hv); exists (x##v); auto.
        - intros (v & Hv); revert Hv; vec split v with x; exists v, x; auto.
      * unfold T; apply IHn, fol_def_ex, HR.
  Qed.

  Fact fol_def_finite_fa I (R : I -> forall X, fo_model Σ X -> (nat -> X) -> Prop) :
            finite_t I
         -> (forall i, fol_definable ls lr (R i))
         -> fol_definable ls lr (fun X M φ => forall i : I, R i X M φ).
  Proof.
    intros (l & Hl) H.
    apply fol_def_equiv with (R := fun X M φ => forall i, In i l -> R i X M φ).
    + intros X M phi; apply forall_equiv; intro; split; auto.
    + apply fol_def_list_fa; auto.
  Qed.

  Fact fol_def_finite_ex I (R : I -> forall X, fo_model Σ X -> (nat -> X) -> Prop) :
            finite_t I
         -> (forall i, fol_definable ls lr (R i))
         -> fol_definable ls lr (fun X M φ => exists i : I, R i X M φ).
  Proof.
    intros (l & Hl) H.
    apply fol_def_equiv with (R := fun X M φ => exists i, In i l /\ R i X M φ).
    + intros X M phi; apply exists_equiv; intro; split; auto; tauto.
    + apply fol_def_list_ex; auto.
  Qed.
 
End extra.

Section fol_def_rsem.

  Variable (sy : Type) (ar : sy -> nat)
           (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ)).

  Let env_vec X (φ : nat -> X) n := vec_set_pos (fun p => φ (@pos2nat n p)).
  Let env_env X (φ : nat -> X) n k := φ (n+k).

  Variable (R : forall X, fo_model Σ X -> forall s, vec X (ar s) -> X -> Prop).

  Hypothesis H0 : fol_definable ls lr (fun X M φ => φ 0 = φ 1).
  Hypothesis HR : forall s, fol_definable ls lr (fun X M φ => R M (env_vec φ (ar s)) (env_env φ (ar s) 0)).

  Theorem fol_def_rsem (t : fo_term nat ar) : 
    fol_definable ls lr (fun X M φ => fo_term_rsem (R M) (fun n r => r = φ (S n)) t (φ 0)).
  Proof.
    induction t as [ n | s v IHv ] using fo_term_pos_rect.
    + apply fol_def_equiv with (R := fun X M phi => phi 0 = phi (S n)).
      * intros ? ? phi; rew fot; tauto.
      * apply (@fol_def_subst2 _ ls lr) with (R := fun X M => @eq X) (1 := H0); fol def.
    + apply fol_def_equiv 
      with (R := fun X M phi => exists w, R M w (phi 0) 
                                       /\ forall p, fo_term_rsem (R M) (fun n r => r = phi (S n)) (vec_pos v p) (vec_pos w p)).
      { symmetry; apply fo_term_rsem_fix_1. }
      apply fol_def_vec_ex.
      apply fol_def_conj; auto.
      1: apply HR.
      apply fol_def_finite_fa.
      * apply finite_t_pos.
      * intros p; specialize (IHv p).
        unfold env_vec, env_env.
        apply fol_def_equiv with (R := fun X M φ => fo_term_rsem (R M) (fun n r => r = φ (ar s + S n)) (vec_pos v p) (φ (pos2nat p))).
        - intros X M phi; rew vec; tauto.
        - apply fol_def_subst with (f := fun n => 
                match n with 
                  | 0   => fun _ _ phi => phi (pos2nat p)
                  | _   => fun _ _ phi => phi (ar s + n)
                end) in IHv; auto.
          intros []; fol def.
  Qed.

End fol_def_rsem.

Check fol_def_rsem.



