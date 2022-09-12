(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat.

Import fol_notations.

Set Implicit Arguments.

(* * From binary singleton to a n-ary function and a unary relation *)

Local Notation ø := vec_nil.
Local Notation Σ2 := (Σrel 2).

Definition Σn1 (n : nat) : fo_signature.
Proof.
  exists unit unit.
  + exact (fun _ => n).
  + exact (fun _ => 1).
Defined.

Local Definition PSSn1 n (x y : nat) := @fol_atom (Σn1 (S (S n))) tt ((@in_fot  _ (ar_syms (Σn1 (S (S n)))) tt (£x##vec_set_pos (fun _ => £y)))##ø).

Section Sig2_SigSSn1_encoding.

  Variable n : nat.

  Fixpoint Σ2_ΣSSn1 (d : nat) (A : fol_form Σ2) : fol_form (Σn1 (S (S n))) :=
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => PSSn1 n (Σrel_var (vec_head v)) (Σrel_var (vec_head (vec_tail v))) 
      | fol_bin b A B  => fol_bin b (Σ2_ΣSSn1 d A) (Σ2_ΣSSn1 d B)
      | fol_quant fol_fa A  => ∀ PSSn1 n (S d) 0 ⤑ Σ2_ΣSSn1 (S d) A
      | fol_quant fol_ex A  => ∃ PSSn1 n (S d) 0 ⟑ Σ2_ΣSSn1 (S d) A
    end.

  Variable (X : Type) (M2  : fo_model Σ2 X).
  Variable (Y : Type) (MSSn1 : fo_model (Σn1 (S (S n))) Y).

  Let Q x1 x2 := fom_rels M2 tt (x1##x2##ø).
  Let f y1 y2 := fom_syms MSSn1 tt (y1##vec_set_pos (fun _ => y2)).
  Let P y := fom_rels MSSn1 tt (y##ø).

  Variable R : X -> Y -> Prop.

  Variable (d : nat) (φ : nat -> X) (ψ : nat -> Y)
           (H1 : forall x1 x2 y1 y2, R x1 y1 -> R x2 y2 -> Q x1 x2 <-> P (f y1 y2))
           (H2 : forall x, exists y, R x y /\ P (f (ψ d) y))
           (H3 : forall y, P (f (ψ d) y) -> exists x, R x y).

  Theorem Σ2_ΣSSn1_correct A : 
           (forall x, In x (fol_vars A) -> R (φ x) (ψ x))
        -> fol_sem M2 φ A <-> fol_sem MSSn1 ψ (Σ2_ΣSSn1 d A).
  Proof.
    revert d φ ψ H2 H3.
    induction A as [ | [] v | b A HA B HB | [] A HA ];
      intros d φ ψ H2 H3 H.
    + simpl; tauto.
    + simpl in v; revert H.
      vec split v with x1; vec split v with x2; vec nil v; clear v.
      revert x1 x2; intros [ x1 | [] ] [ x2 | [] ] H; simpl in H.
      unfold Q in H1; simpl fol_sem at 1.
      rewrite H1.
      2-3: apply H; auto.
      unfold P, f; simpl.
      apply fol_equiv_ext; do 5 f_equal.
      apply vec_pos_ext; intro p.
      rewrite vec_pos_map; rew vec.
    + simpl; apply (fol_bin_sem_ext _).
      * apply HA; auto; intros; apply H, in_app_iff; auto.
      * apply HB; auto; intros; apply H, in_app_iff; auto.
    + simpl; split.
      * intros (x & Hx).
        destruct (H2 x) as (y & Hy1 & Hy2).
        exists y; split; auto.
        - revert Hy2; unfold P, f; simpl.
          apply fol_equiv_ext; do 5 f_equal.
          apply vec_pos_ext; intro p.
          rewrite vec_pos_map; rew vec.
        - revert Hx; apply HA; simpl; auto.
          intros [|i] Hi; simpl; auto.
          apply H; simpl; apply in_flat_map.
          exists (S i); simpl; auto.
      * intros (y & G1 & G2).
        destruct (H3 y) as (x & Hx).
        - revert G1; unfold P, f; simpl.
          apply fol_equiv_ext; do 5 f_equal.
          apply vec_pos_ext; intro p.
          rewrite vec_pos_map; rew vec.
        - exists x; revert G2; apply HA; simpl; auto.
          intros [|i] Hi; simpl; auto.
          apply H; simpl; apply in_flat_map.
          exists (S i); simpl; auto.
    + simpl; split.
      * intros G y Hy.
        destruct (H3 y) as (x & Hx).
        - revert Hy; unfold P, f; simpl.
          apply fol_equiv_ext; do 5 f_equal.
          apply vec_pos_ext; intro p.
          rewrite vec_pos_map; rew vec.
        - generalize (G x); apply HA; simpl; auto.
          intros [|i] Hi; simpl; auto.
          apply H; simpl; apply in_flat_map.
          exists (S i); simpl; auto.
      * intros G x.
        destruct (H2 x) as (y & Hy1 & Hy2).
        specialize (G y). 
        spec in G.
        - revert Hy2; unfold P, f; simpl.
          apply fol_equiv_ext; do 5 f_equal.
          apply vec_pos_ext; intro p.
          rewrite vec_pos_map; rew vec.
        - revert G; apply HA; simpl; auto.
          intros [|i] Hi; simpl; auto.
          apply H; simpl; apply in_flat_map.
          exists (S i); simpl; auto.
  Qed.

End Sig2_SigSSn1_encoding.

Section Σ2_ΣSSn1_enc.

  Variable (n : nat) (A : fol_form Σ2).

  Let d := S (lmax (fol_vars A)).

  Definition Σ2_ΣSSn1_enc := fol_lconj (map (PSSn1 n d) (fol_vars A))
                            ⟑ PSSn1 n d 0
                            ⟑ Σ2_ΣSSn1 n d A.

End Σ2_ΣSSn1_enc.

Section Σ2_ΣSSn1_enc_sound.

  Variable (n : nat) (A : fol_form Σ2) (X : Type) (M2 : fo_model Σ2 X) (φ : nat -> X)
           (HA : fol_sem M2 φ A).

  Let Y := (bool + X + X*X)%type.

  Let i := S (lmax (fol_vars A)).

  Let d : Y := inl (inl true).

  Let MSSn1 : fo_model (Σn1 (S (S n))) Y.
  Proof.
    split.
    + simpl; intros _ v.
      exact (match (vec_head v), (vec_head (vec_tail v)) with
        | inl (inl true), inl (inr x)  => inl (inr x)
        | inl (inr x1),   inl (inr x2) => inr (x1,x2)
        | _           ,   _            => inl (inl false)
      end).
    + simpl; intros _ v.
      exact (match vec_head v with
        | inl (inr _) => True
        | inr (x1,x2) => fom_rels M2 tt (x1##x2##ø)
        | _           => False
      end).
  Defined.

  Let ψ n : Y := 
    if eq_nat_dec i n then d else inl (inr (φ n)).

  Let phi_i : ψ i = d.
  Proof.
    unfold ψ.
    destruct (eq_nat_dec i i) as [ | [] ]; auto.
  Qed.

  Let phi_x j : In j (fol_vars A) -> ψ j = inl (inr (φ j)).
  Proof.
    intros H.
    assert (D : lmax (fol_vars A) < i).
    { apply le_refl. }
    unfold ψ.
    destruct (eq_nat_dec i j); auto.
    apply lmax_prop in H; lia.
  Qed.

  Let R x (y : Y) := y = inl (inr x).

  Let sem_Σ2_ΣSSn1_enc : fol_sem MSSn1 ψ (Σ2_ΣSSn1_enc n A).
  Proof.
    simpl; msplit 2.
    - rewrite fol_sem_lconj; intros ?; rewrite in_map_iff.
      intros (j & <- & Hj); simpl.
      fold i; rewrite phi_i; simpl.
      rewrite phi_x; auto.
    - fold i; rewrite phi_i; simpl; auto.
    - revert HA; apply Σ2_ΣSSn1_correct with (R := R).
      + intros x1 x2 y1 y2; unfold R; simpl; intros -> ->; tauto.
      + intros x; exists (inl (inr x)); split.
        * red; auto.
        * fold i; rewrite phi_i; unfold d; simpl; auto.
      + fold i; rewrite phi_i; intros [ [ [] | x ] | (x1,x2) ]; simpl; try tauto.
        exists x; red; auto.
      + intros j Hj; rewrite (phi_x _ Hj); red; auto.
  Qed.

  Hypothesis (HX : finite_t X)
             (M2_dec : fo_model_dec M2).

  Hint Resolve finite_t_sum finite_t_bool finite_t_prod : core.

  Theorem Σ2_ΣSSn1_enc_sound : fo_form_fin_dec_SAT (Σ2_ΣSSn1_enc n A).
  Proof.
    exists Y, MSSn1.
    exists. { unfold Y; auto. }
    exists.
    { intros []; simpl; intros v.
      vec split v with x; vec nil v; clear v; simpl.
      destruct x as [ [ [] | x ] | (x1,x2) ]; try tauto.
      apply M2_dec. }
    exists ψ; auto.
  Qed.

End Σ2_ΣSSn1_enc_sound.

Section Σ2_ΣSSn1_enc_complete.
 
  Variable (n : nat) (A : fol_form Σ2) (Y : Type) (MSSn1 : fo_model (Σn1 (S (S n))) Y)
           (MSSn1_dec : fo_model_dec MSSn1) (ψ : nat -> Y).

  Let i := S (lmax (fol_vars A)).
  Let d := ψ i.

  Let f u v := fom_syms MSSn1 tt (u##vec_set_pos (fun _ => v)).

  Let P y := fom_rels MSSn1 tt (f d y##ø).
          
  Hypothesis (HA : fol_sem MSSn1 ψ (Σ2_ΣSSn1_enc n A)).

  Let Q y := (if @MSSn1_dec tt (f d y##ø) then true else false) = true.

  Let Q_spec y : Q y <-> P y.
  Proof.
    unfold P, Q.
    destruct (MSSn1_dec (f d y##ø)); split; auto; discriminate.
  Qed.

  Let H1 j : In j (fol_vars A) -> Q (ψ j).
  Proof.
    intros Hj; apply Q_spec.
    simpl in HA; apply proj1 in HA.
    rewrite fol_sem_lconj in HA.
    unfold P.
    specialize (HA (PSSn1 n i j)).
    spec in HA.
    - apply in_map_iff.
      exists j; split; auto.
    - revert HA; apply fol_equiv_ext.
      unfold f; simpl; do 5 f_equal.
      apply vec_pos_ext; intro p.
      rewrite vec_pos_map; rew vec.
  Qed.

  Let H2 : Q (ψ 0).
  Proof. 
    apply Q_spec.
    unfold P, f.
    simpl in HA.
    apply proj2, proj1 in HA.
    revert HA.
    apply fol_equiv_ext.
    simpl; do 5 f_equal.
    apply vec_pos_ext; intro p.
    rewrite vec_pos_map; rew vec.
  Qed.

  Let H3 : fol_sem MSSn1 ψ (Σ2_ΣSSn1 n i A).
  Proof. apply HA. Qed.

  Let X := sig Q.

  Let M2 : fo_model Σ2 X.
  Proof.
    split.
    + intros [].
    + intros r; simpl; intros v.
      exact (fom_rels MSSn1 tt (f (proj1_sig (vec_head v)) (proj1_sig (vec_head (vec_tail v)))##ø)).
  Defined.

  Let φ n : X :=
    match in_dec eq_nat_dec n (fol_vars A) with
      | left H  => exist _ _ (H1 n H)
      | right _ => exist _ _ H2
    end.

  Let R (x : X) (y : Y) := proj1_sig x = y.

  Let sem_A : fol_sem M2 φ A.
  Proof.
    revert H3; apply Σ2_ΣSSn1_correct with (R := R).
    + intros (x1 & E1) (x2 & E2) y1 y2; unfold R; simpl.
      intros <- <-; tauto.
    + intros (x & Hx); exists x; split.
      * red; simpl; auto.
      * apply Q_spec in Hx; auto.
    + intros y Hy; apply Q_spec in Hy.
      exists (exist _ y Hy); red; auto.
    + intros j Hj; unfold φ.
      destruct (in_dec eq_nat_dec j (fol_vars A)) as [ | [] ]; auto.
      red; simpl; auto.
  Qed.

  Hypothesis HY : finite_t Y.

  Theorem Σ2_ΣSSn1_enc_complete : fo_form_fin_dec_SAT A.
  Proof.
    exists X, M2.
    exists. 
    { unfold X; apply fin_t_finite_t.
      + intros; apply eq_bool_pirr.
      + unfold Q; apply finite_t_fin_t_dec; auto.
        intros; apply bool_dec. }
    exists.
    { intros [] v; simpl; apply MSSn1_dec. }
    exists φ; auto. 
  Qed.

End Σ2_ΣSSn1_enc_complete.




