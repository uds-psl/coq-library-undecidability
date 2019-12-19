(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat
                 membership hfs rels_hfs Sig2.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Fact nat_pos_rect (P : nat -> Type) n :
           (forall p : pos n, P (pos2nat p))
        -> (forall i, P (i+n))
        -> forall i, P i.
Proof.
  intros H1 H2 i.
  destruct (le_lt_dec n i) as [ H | H ].
  + replace i with ((i-n)+n) by lia; apply H2.
  + rewrite <- (pos2nat_nat2pos H); apply H1.
Qed.

Section Sig_Sig2_encoding.

  Variable (Σ : fo_signature).

  Notation Σ2 := (Σrel 2).

  Infix "∈" := Σ2_mem.
  Infix "≈" := Σ2_equiv.
  Infix "⊆" := Σ2_incl.

  Notation 𝕋 := (fol_term Σ).
  Notation 𝔽 := (fol_form Σ).

  Notation 𝕋2 := (fol_term Σ2).
  Notation 𝔽2 := (fol_form Σ2).

  Section removing_symbols_from_terms.

    Variable (ρ : syms Σ -> nat)
             (µ : rels Σ -> nat)
             (d : nat).

    Local Fixpoint fot_rem_syms r n (t : 𝕋) : 𝔽2 :=
      match t with
        | in_var i   => r ≈ i+n
        | in_fot s v => let a := ar_syms _ s
                     in let v1 := vec_set_pos (fun p : pos a 
                              => fot_rem_syms (pos2nat p) (n+a) (vec_pos v p))
                     in let v2 := vec_set_pos (fun p : pos a
                              => pos2nat p ∈ d+n+a)
                     in let w := vec_set_pos (fun p : pos a => pos2nat p)
                     in let A := Σ2_is_tuple_in (ρ s+n+a) (r+a##w)
                     in let B := fol_vec_fa v1
                     in let C := fol_vec_fa v2
                     in fol_mquant fol_ex (ar_syms _ s) (A ⟑ B ⟑ C)
      end.

    Local Fact for_rem_syms r n t i : In i (fol_vars (fot_rem_syms r n t)) 
                             -> i = r \/ (exists j, i = j+n /\ In j (d::fo_term_vars t))
                                      \/ (exists s, i = ρ s+n /\ In s (fo_term_syms t)).
    Proof.
      revert r n i; induction t as [ j | s v IH ]; intros r n i.
      + simpl; repeat (intros [ <- | H ]; [ | revert H]); try tauto; right; left; exists j; auto.
      + simpl fot_rem_syms.
        rewrite fol_vars_mquant, in_flat_map.
        intros (x & H1 & H2).
        rewrite !fol_vars_bin, !in_app_iff, !fol_vars_vec_fa, !in_flat_map in H1.
        revert H1; intros [ H1 | [ (y & H1 & H3) | (y & H1 & H3) ] ].
        * apply Σ2_is_tuple_in_vars in H1; simpl in H1.
          rewrite vec_list_vec_set_pos, in_map_iff in H1.
          destruct H1 as [ <- | [ <- | (p & <- & Hp) ] ].
          - destruct (le_lt_dec (ar_syms Σ s) (ρ s + n + ar_syms Σ s)); try lia.
            destruct H2 as [ <- | [] ].
            do 2 right; exists s; split; try lia; simpl; auto.
          - destruct (le_lt_dec (ar_syms Σ s) (r + ar_syms Σ s)); try lia.
            destruct H2 as [ <- | [] ]; left; lia.
          - destruct (le_lt_dec (ar_syms Σ s) (pos2nat p)); simpl in H2; try tauto. 
            generalize (pos2nat_prop p); try lia.
        * rewrite vec_list_vec_set_pos, in_map_iff in H1.
          destruct H1 as (p & <- & H1).
          apply IH in H3.
          destruct H3 as [ -> | [ (j & -> & H3) | (s' & -> & H3) ] ].
          - destruct (le_lt_dec (ar_syms Σ s) (pos2nat p)); simpl in H2; try tauto.
            generalize (pos2nat_prop p); try lia.
          - destruct (le_lt_dec (ar_syms Σ s) (j + (n + ar_syms Σ s))); try lia.
            destruct H2 as [ <- | [] ].
            right; left; exists j; split; try lia. 
            destruct H3 as [ H3 | H3 ]; try (simpl; auto; fail); right.
            rew fot; rewrite in_flat_map.
            exists (vec_pos v p); split; auto.
            apply in_vec_list, in_vec_pos.
          - destruct (le_lt_dec (ar_syms Σ s) (ρ s' + (n + ar_syms Σ s))); try lia.
            destruct H2 as [ <- | [] ].
            do 2 right; exists s'; split; try lia.
            rew fot; simpl; rewrite in_flat_map.
            right; exists (vec_pos v p); split; auto.
            apply in_vec_list, in_vec_pos.
        * rewrite vec_list_vec_set_pos, in_map_iff in H1.
          destruct H1 as (p & <- & H1).
          simpl in H3.
          destruct H3 as [ <- | [ <- | [] ] ].
          - destruct (le_lt_dec (ar_syms Σ s) (pos2nat p)); simpl in H2; try tauto.
            generalize (pos2nat_prop p); try lia.
          - destruct (le_lt_dec (ar_syms Σ s) (d + n + ar_syms Σ s)); try lia.
            destruct H2 as [ <- | [] ].
            right; left; exists d; split; simpl; auto; lia.
    Qed.

    Local Definition fol_rem_atom n (s : rels Σ) (vt : vec 𝕋 (ar_rels _ s) ) : 𝔽2 :=
         let a := ar_rels _ s
      in let v1 := vec_set_pos (fun p : pos a 
              => fot_rem_syms (pos2nat p) (n+a) (vec_pos vt p))
      in let v2 := vec_set_pos (fun p : pos a
              => pos2nat p ∈ d+n+a)
      in let w := vec_set_pos (fun p : pos a => pos2nat p)
      in let A := Σ2_is_tuple_in (µ s+n+a) w
      in let B := fol_vec_fa v1
      in let C := fol_vec_fa v2
      in fol_mquant fol_ex a (A ⟑ B ⟑ C).

    Fact fol_rem_atom_vars n s vt i : In i (fol_vars (fol_rem_atom n s vt))
                                   ->    (exists j, i = j+n /\ In j (d::flat_map fo_term_vars (vec_list vt)))
                                      \/ (exists s, i = ρ s+n /\ In s (flat_map fo_term_syms (vec_list vt)))
                                      \/ i = µ s+n.
    Proof.
      unfold fol_rem_atom.
      rewrite fol_vars_mquant, in_flat_map.
      intros (x & H1 & H2); revert H1.
      rewrite !fol_vars_bin, !in_app_iff, !fol_vars_vec_fa, !in_flat_map.
      intros [ H1 | [ (y & H1 & H3) | (y & H1 & H3) ] ].
      + apply Σ2_is_tuple_in_vars in H1; simpl in H1.
        rewrite vec_list_vec_set_pos, in_map_iff in H1.
        destruct H1 as [ <- | (p & <- & Hp) ].
        * destruct (le_lt_dec (ar_rels Σ s) (µ s + n + ar_rels Σ s)); try lia.
          destruct H2 as [ <- | [] ].
          do 2 right; lia.
        * destruct (le_lt_dec (ar_rels Σ s) (pos2nat p)); simpl in H2; try tauto. 
          generalize (pos2nat_prop p); try lia.
      + rewrite vec_list_vec_set_pos, in_map_iff in H1.
        destruct H1 as (p & <- & H1).
        apply for_rem_syms in H3.
        destruct H3 as [ -> | [ (j & -> & H3) | (s' & -> & H3) ] ].
        * destruct (le_lt_dec (ar_rels Σ s) (pos2nat p)); simpl in H2; try tauto. 
          generalize (pos2nat_prop p); try lia.
        * destruct (le_lt_dec (ar_rels Σ s) (j + (n + ar_rels Σ s))); try lia.
          destruct H2 as [ <- | [] ].
          left; exists j; split; try lia.
          destruct H3 as [ H3 | H3 ]; subst; try (simpl; auto; fail); right.
          apply in_flat_map.
          exists (vec_pos vt p); split; auto.
          apply in_vec_list, in_vec_pos.
        * destruct (le_lt_dec (ar_rels Σ s) (ρ s' + (n + ar_rels Σ s))); try lia.
          destruct H2 as [ <- | [] ].
          right; left; exists s'; split; try lia.
          apply in_flat_map.
          exists (vec_pos vt p); split; auto.
          apply in_vec_list, in_vec_pos.
      + rewrite vec_list_vec_set_pos, in_map_iff in H1.
        destruct H1 as (p & <- & H1).
        simpl in H3.
        destruct H3 as [ <- | [ <- | [] ] ].
        - destruct (le_lt_dec (ar_rels Σ s) (pos2nat p)); simpl in H2; try tauto.
          generalize (pos2nat_prop p); try lia.
        - destruct (le_lt_dec (ar_rels Σ s) (d + n + ar_rels Σ s)); try lia.
          destruct H2 as [ <- | [] ].
          left; exists d; simpl; split; auto; lia.
    Qed.

    Variable (X : Type) (MX : fo_model Σ X)
             (Y : Type) (MY : fo_model Σ2 Y) (dy : Y).

    Let mem x y := fom_rels MY tt (x##y##ø).

    Hypothesis (HY1 : mb_member_ext mem)
               (HY2 : forall u v, mb_equiv mem u v <-> u = v).

    Hypothesis (f : X -> Y) (g : Y -> X) 
               (Hfg1 : forall x, mem (f x) dy)
               (Hfg2 : forall y, mem y dy -> exists x, y = f x) 
               (Hfg3 : forall x, g (f x) = x).

    Let f_equiv u v : u = v <-> f u = f v.
    Proof.
      split.
      + intros []; auto.
      + intros H; rewrite <- (Hfg3 u), H, Hfg3; auto.
    Qed.

    Hypothesis (φ : nat -> X).

    Theorem fot_rem_syms_sem t r x ψ n :
                                   (forall s v x,   In s (fo_term_syms t)
                                    ->  x = fom_syms MX s v 
                                   <-> mb_is_tuple_in mem (ψ (ρ s+n)) (f x##vec_map f v))
                                -> (forall i, In i (fo_term_vars t) -> ψ (i+n) = f (φ i))
                                -> ψ (d+n) = dy
                                -> ψ r = f x
                                -> x = fo_term_sem MX φ t
                               <-> fol_sem MY ψ (fot_rem_syms r n t).
    Proof.
      revert r n ψ x.
      induction t as [ i | s vt IH ]; intros r n ψ x Hρ H1 H3 H2.
      + simpl fot_rem_syms.
        rewrite Σ2_equiv_spec. 
        unfold mem in HY2. 
        rewrite HY2; rew fot.
        rewrite H1, H2. 
        apply f_equiv.
        rew fot; simpl; auto.
      + simpl fot_rem_syms.
        rewrite fol_sem_mexists.
        split.
        * rew fot; intros E.
          exists (vec_map (fun t => f (fo_term_sem MX φ t)) vt).
          msplit 2.
          - rewrite Σ2_is_tuple_in_spec.
            simpl vec_map; simpl env_vlift.
            rewrite !env_vlift_fix1.
            rewrite vec_map_set_pos.
            match goal with
              | |- mb_is_tuple_in _ _ (_##?t) => assert (H : t = vec_map f (vec_map (fo_term_sem MX φ) vt))
            end.
            { apply vec_pos_ext; intros p; rew vec.
              rewrite env_vlift_fix0; rew vec. }
            rewrite H; clear H.
            rewrite H2.
            apply Hρ; auto.
            rew fot; simpl; auto.
          - rewrite fol_sem_vec_fa; intros p.
            rew vec; simpl.
            rewrite <- IH.
            ++ reflexivity.
            ++ intros; rewrite plus_assoc, env_vlift_fix1; auto.
               apply Hρ; rew fot; right; apply in_flat_map.
               exists (vec_pos vt p); split; auto.
               apply in_vec_list, in_vec_pos.
            ++ intros i Hi; rewrite plus_assoc, env_vlift_fix1; auto.
               apply H1; rew fot; apply in_flat_map.
               exists (vec_pos vt p); split; auto.
               apply in_vec_list, in_vec_pos.
            ++ rewrite plus_assoc, env_vlift_fix1; auto. 
            ++ rewrite env_vlift_fix0; rew vec.
          - rewrite fol_sem_vec_fa; intros p; rew vec; simpl.
            rewrite env_vlift_fix0, env_vlift_fix1; rew vec.
            rewrite H3; apply Hfg1.
        * intros (w & H4 & H5 & H6).
          rewrite Σ2_is_tuple_in_spec in H4; simpl in H4.
          rewrite !env_vlift_fix1 in H4.
          rewrite vec_map_set_pos in H4.
          replace (vec_set_pos (fun p : pos (ar_syms Σ s) => env_vlift ψ w (pos2nat p)))
            with w in H4.
          2: apply vec_pos_ext; intro; rew vec; rewrite env_vlift_fix0; auto.
          rewrite H2 in H4.
          rewrite fol_sem_vec_fa in H6.
          assert (H7: forall p, mem (vec_pos w p) dy).
          { intros p; generalize (H6 p); rew vec; simpl.
            rewrite env_vlift_fix0, env_vlift_fix1, H3; auto. }
          clear H6.
          assert (H8: forall p, exists x, vec_pos w p = f x).
          { intros; apply Hfg2; auto. }
          apply vec_reif in H8.
          destruct H8 as (v' & H8).
          rewrite fol_sem_vec_fa in H5.
          assert (H6: forall p, fol_sem MY (env_vlift ψ w) (fot_rem_syms (pos2nat p) (n + ar_syms _ s) (vec_pos vt p))).
          { intros p; generalize (H5 p); rew vec. }
          clear H5.
          assert (H5 : forall p, vec_pos v' p = fo_term_sem MX φ (vec_pos vt p)).
          { intros p.
            generalize (H6 p).
            apply IH; auto.
            + intros s' v x' H.
              rewrite plus_assoc, env_vlift_fix1.
              apply Hρ; rew fot; right; apply in_flat_map.
              exists (vec_pos vt p); split; auto.
              apply in_vec_list, in_vec_pos.
            + intros i Hi; rewrite plus_assoc, env_vlift_fix1; auto.
              apply H1; rew fot; apply in_flat_map.
              exists (vec_pos vt p); split; auto.
              apply in_vec_list, in_vec_pos.
            + rewrite plus_assoc, env_vlift_fix1; auto.
            + rewrite env_vlift_fix0; auto. }
          rew fot.
          apply Hρ; auto.
          - rew fot; simpl; auto.
          - rewrite vec_map_map.
            revert H4.
            apply fol_equiv_ext; do 2 f_equal.
            apply vec_pos_ext; intros p; rew vec.
            rewrite H8, H5; auto.
    Qed.

    Hypothesis (ψ : nat -> Y) (s : rels Σ) (vt : vec 𝕋 (ar_rels _ s))
               (Hρ : forall s' v x,  In s' (flat_map fo_term_syms (vec_list vt))
                                 -> x = fom_syms MX s' v 
                                <-> mb_is_tuple_in mem (ψ (ρ s')) (f x##vec_map f v))
               (Hµ : forall v, fom_rels MX s v 
                 <-> mb_is_tuple_in mem (ψ (µ s)) (vec_map f v))
               (H1 : forall i, In i (flat_map fo_term_vars (vec_list vt)) -> ψ i = f (φ i))
               (H2 : ψ d = dy).

    Theorem fol_rem_atom_sem : fol_sem MX φ (fol_atom s vt)
                           <-> fol_sem MY ψ (fol_rem_atom 0 s vt).
    Proof.
      simpl; rewrite Hµ; auto.
      unfold fol_rem_atom. 
      rewrite fol_sem_mexists.
      split; auto.
      + intros H.
        exists (vec_map (fun t => f (fo_term_sem MX φ t)) vt).
        msplit 2.
        * rewrite Σ2_is_tuple_in_spec.
          rewrite env_vlift_fix1.
          revert H; apply fol_equiv_ext; f_equal.
          - f_equal; lia.
          - apply vec_pos_ext; intros p; rew vec.
            rewrite env_vlift_fix0; rew vec.
        * rewrite fol_sem_vec_fa; intros p; rew vec.
          rewrite <- fot_rem_syms_sem.
          - reflexivity.
          - intros; rewrite plus_assoc, env_vlift_fix1; auto.
            rewrite plus_comm; simpl; auto.
            apply Hρ, in_flat_map.
            exists (vec_pos vt p); split; auto.
            apply in_vec_list, in_vec_pos.
          - intros i Hi; simpl.
            rewrite env_vlift_fix1; auto.
            apply H1, in_flat_map.
            exists (vec_pos vt p); split; auto.
            apply in_vec_list, in_vec_pos.
          - simpl; rewrite env_vlift_fix1; auto.
          - rewrite env_vlift_fix0; rew vec.
        * rewrite fol_sem_vec_fa; intros p; rew vec.
          simpl; rewrite env_vlift_fix0, env_vlift_fix1; rew vec.
          rewrite plus_comm; simpl.
          rewrite H2; apply Hfg1.
      + intros (w & H3 & H4 & H5).
        rewrite Σ2_is_tuple_in_spec in H3; simpl in H3.
        rewrite  Nat.add_0_r, !env_vlift_fix1 in H3.
        rewrite vec_map_set_pos in H3.
        replace (vec_set_pos (fun p : pos (ar_rels _ s) => env_vlift ψ w (pos2nat p)))
          with w in H3.
        2: apply vec_pos_ext; intro; rew vec; rewrite env_vlift_fix0; auto.
        rewrite fol_sem_vec_fa in H5.
        assert (H7: forall p, mem (vec_pos w p) dy).
        { intros p; generalize (H5 p); rew vec; simpl.
          rewrite Nat.add_0_r, env_vlift_fix0, env_vlift_fix1, H2; auto. }
        clear H5.
        assert (H8: forall p, exists x, vec_pos w p = f x).
        { intros; apply Hfg2; auto. }
        apply vec_reif in H8.
        destruct H8 as (v' & H8).
        rewrite fol_sem_vec_fa in H4.
        assert (H6: forall p, fol_sem MY (env_vlift ψ w) (fot_rem_syms (pos2nat p) (ar_rels _ s) (vec_pos vt p))).
        { intros p; generalize (H4 p); rew vec. }
        clear H4.
        assert (H5 : forall p, vec_pos v' p = fo_term_sem MX φ (vec_pos vt p)).
        { intros p.
          generalize (H6 p).
          apply fot_rem_syms_sem; auto.
          + intros; rewrite env_vlift_fix1; auto.
            apply Hρ, in_flat_map.
            exists (vec_pos vt p); split; auto.
            apply in_vec_list, in_vec_pos.
          + intros i Hi; rewrite env_vlift_fix1.
            apply H1, in_flat_map.
            exists (vec_pos vt p); split; auto.
            apply in_vec_list, in_vec_pos. 
          + rewrite env_vlift_fix1; auto.
          + rewrite env_vlift_fix0; auto. }
        rew fot.
        revert H3.
        apply fol_equiv_ext; do 2 f_equal.
        apply vec_pos_ext; intros p; rew vec.
        rewrite H8, H5; auto.
    Qed.

  End removing_symbols_from_terms.

  Section all.

    Implicit Types (ρ : syms Σ -> nat)
                   (µ : rels Σ -> nat)
                   (d : nat).

    Fixpoint Σ_Σ2 ρ µ d (A : 𝔽) : 𝔽2 :=
      match A with
        | ⊥              => ⊥
        | fol_atom s v   => fol_rem_atom ρ µ d 0 s v 
        | fol_bin b A B  => fol_bin b (Σ_Σ2 ρ µ d A) (Σ_Σ2 ρ µ d B)
        | ∀ A            => ∀ 0 ∈ (S d) ⤑ Σ_Σ2 (fun s => S (ρ s)) (fun s => S (µ s)) (S d) A
        | ∃ A            => ∃ 0 ∈ (S d) ⟑ Σ_Σ2 (fun s => S (ρ s)) (fun s => S (µ s)) (S d) A
      end.

    Fact Σ_Σ2_vars ρ µ d A : incl (fol_vars (Σ_Σ2 ρ µ d A)) 
                                  (d::fol_vars A++map ρ (fol_syms A)++map µ (fol_rels A)).
    Proof.
      revert ρ µ d; induction A as [ | r v | b A HA B HB | [] A HA ]; intros ρ µ d i Hi.
      + destruct Hi.
      + apply fol_rem_atom_vars in Hi.
        simpl; rewrite !in_app_iff.
        destruct Hi as [ (j & -> & [ <- | Hj ]) | [ (s' & -> & Hs') | -> ] ]; rewrite <- plus_comm; simpl; auto.
        right; right; left; apply in_map_iff; exists s'; auto.
      + simpl in *; rewrite !in_app_iff in *.
        destruct Hi as [ Hi | Hi ]; [ apply HA in Hi | apply HB in Hi ];
          simpl in *; rewrite !map_app, !in_app_iff in *; tauto.
      + simpl in *; rewrite !in_app_iff, !in_flat_map, !in_map_iff in *.
        destruct Hi as [ Hi | (x & Hi & H2) ]; auto.
        apply HA in Hi.
        simpl in *; rewrite !in_app_iff, !in_map_iff in *. 
        destruct Hi as [ <- | [ Hi | [ (s' & <- & Hi) | (s' & <- & Hi) ] ] ].
        * simpl in H2; tauto.
        * right; left; exists x; auto.
        * destruct H2 as [ <- | [] ]; right; right; left; exists s'; auto.
        * destruct H2 as [ <- | [] ]; right; right; right; exists s'; auto.
      + simpl in *; rewrite !in_app_iff, !in_flat_map, !in_map_iff in *.
        destruct Hi as [ Hi | (x & Hi & H2) ]; auto.
        apply HA in Hi.
        simpl in *; rewrite !in_app_iff, !in_map_iff in *. 
        destruct Hi as [ <- | [ Hi | [ (s' & <- & Hi) | (s' & <- & Hi) ] ] ].
        * simpl in H2; tauto.
        * right; left; exists x; auto.
        * destruct H2 as [ <- | [] ]; right; right; left; exists s'; auto.
        * destruct H2 as [ <- | [] ]; right; right; right; exists s'; auto.
    Qed.

    Variable (X : Type) (MX : fo_model Σ X)
             (Y : Type) (MY : fo_model Σ2 Y) (dy : Y).

    Let mem x y := fom_rels MY tt (x##y##ø).

    Hypothesis (HY1 : mb_member_ext mem)
               (HY2 : forall u v, mb_equiv mem u v <-> u = v).

    Hypothesis (f : X -> Y) (g : Y -> X) 
               (Hfg1 : forall x, mem (f x) dy)
               (Hfg2 : forall y, mem y dy -> exists x, y = f x) 
               (Hfg3 : forall x, g (f x) = x).

    Let f_equiv u v : u = v <-> f u = f v.
    Proof.
      split.
      + intros []; auto.
      + intros H; rewrite <- (Hfg3 u), H, Hfg3; auto.
    Qed.

    Hypothesis (ρ : syms Σ -> nat)
               (µ : rels Σ -> nat)
               (d : nat)
               (φ : nat -> X) (ψ : nat -> Y)
               (F : 𝔽)
               (Hφ : forall i, In i (fol_vars F) -> ψ i = f (φ i))
               (Hψ : ψ d = dy)
               (Hρ : forall s v x,  In s (fol_syms F)
                                 -> x = fom_syms MX s v 
                                <-> mb_is_tuple_in mem (ψ (ρ s)) (f x##vec_map f v))
               (Hµ : forall s v,    In s (fol_rels F)
                                 -> fom_rels MX s v 
                                <-> mb_is_tuple_in mem (ψ (µ s)) (vec_map f v)).

    Theorem Σ_Σ2_sem : fol_sem MX φ F
                   <-> fol_sem MY ψ (Σ_Σ2 ρ µ d F).
    Proof.
      revert ρ µ d φ ψ Hρ Hµ Hφ Hψ.
      induction F as [ | r vt | b A HA B HB | [] A HA ]; intros ρ µ d φ ψ Hρ Hµ H1 H2.
      + simpl; tauto.
      + apply fol_rem_atom_sem with (dy := dy) (4 := Hfg3); auto.
        intros; apply Hµ; simpl; auto.
      + simpl Σ_Σ2; rewrite !fol_sem_bin_fix.
        apply fol_bin_sem_ext; [ apply HA | apply HB ]; auto; intros; 
          (apply Hρ || apply Hµ || apply H1 ); apply in_app_iff; auto.
      + simpl; split.
        * intros (x & Hx).
          exists (f x); split.
          - rewrite H2; apply Hfg1.
          - revert Hx; apply HA; auto.
            intros [] ?; simpl; auto.
            apply H1, in_flat_map.
            exists (S n); simpl; auto.
        * intros (y & H3 & H4).
          destruct (Hfg2 y) as (x & Hx).
          - rewrite <- H2; auto.
          - exists x.
            revert H4; apply HA; auto.
            intros [] ?; simpl; auto.
            apply H1, in_flat_map.
            exists (S n); simpl; auto.
      + simpl; split.
        * intros H y Hy.
          rewrite H2 in Hy.
          destruct (Hfg2 _ Hy) as (x & Hx).
          generalize (H x); apply HA; auto.
          intros [] ?; simpl; auto.
          apply H1, in_flat_map.
          exists (S n); simpl; auto.
        * intros H x.
          specialize (H (f x)).
          rewrite H2 in H.
          generalize (H (Hfg1 _)); apply HA; auto.
          intros [] ?; simpl; auto.
          apply H1, in_flat_map.
          exists (S n); simpl; auto.
    Qed.

  End all.

  Hypothesis (Hs : discrete (syms Σ))
             (Hr : discrete (rels Σ)).

  Check Σ_Σ2.
  Check Σ_Σ2_sem.
  Check Σ_Σ2_vars.

  Variable A : fol_form Σ.

  Let Ds := list_discrete_bij_nat (fol_syms A) Hs.
  Let Dr := list_discrete_bij_nat (fol_rels A) Hr.

  Let x0 := 0.
  Let d  := 1.

  Let ns  := projT1 Ds.
  Let ρ s := 2 + projT1 (projT2 Ds) s.

  Let nr  := projT1 Dr.
  Let µ r := 2 + ns + projT1 (projT2 Dr) r.

  Let B := fol_subst (fun i => £ (i+2+ns+nr)) A.

  Definition Σ_Σ2_enc := 
                Σ2_extensional 
              ⟑ x0 ∈ d
              ⟑ Σ2_transitive d
              ⟑ Σ2_list_in d (fol_vars B) 
              ⟑ fol_lconj (map (fun s => Σ2_is_fun d (ρ s) ⟑ Σ2_is_tot (ar_syms _ s) d (ρ s)) (fol_syms A))
              ⟑ Σ_Σ2 ρ µ d B.

  Section SAT2_SAT.

    Variables (Y : Type) 
              (M2 : fo_model (Σrel 2) Y)
              (M2fin : finite_t Y)
              (M2dec : fo_model_dec M2)
              (ψ : nat -> Y)
              (HA : fol_sem M2 ψ Σ_Σ2_enc).

    Let mem a b := fom_rels M2 tt (a##b##ø).

    Infix "∈m" := mem (at level 70).
    Infix "≈m" := (mb_equiv mem) (at level 70).

    Hypothesis Mmem : forall x y, x ≈m y <-> x = y.

    Let mem_dec : forall x y, { x ∈m y } + { ~ x ∈m y }.
    Proof. intros x y; apply (@M2dec tt). Qed.

    Let equiv_refl x : x ≈m x.
    Proof. apply mb_equiv_refl. Qed.

    Let HA0 : mb_member_ext mem.
    Proof. apply HA. Qed.

    Let HA1 : ψ x0  ∈m ψ d.
    Proof. apply HA. Qed.

    Let HA2 : mb_transitive mem (ψ d).
    Proof. apply HA. Qed.

    Let HA3 : forall x, In x (fol_vars B) -> ψ x ∈m ψ d.
    Proof. apply Σ2_list_in_spec, HA. Qed.

    Let HA5 : fol_sem M2 ψ (Σ_Σ2 ρ µ d B).
    Proof. apply HA. Qed.

    Let P x := (if mem_dec x (ψ d) then true else false) = true.

    Let HP0 x : P x <-> mem x (ψ d).
    Proof.
      unfold P.
      destruct (mem_dec x (ψ d)); split; try tauto; discriminate.
    Qed.

    Let X := sig P.

    Let Hx0 : P (ψ x0).
    Proof. apply HP0; auto. Qed.

    Let memX (x y : X) := proj1_sig x ∈m proj1_sig y.

    Let equivX_spec (x y : X) : mb_equiv memX x y <-> mb_equiv mem (proj1_sig x) (proj1_sig y).
    Proof.
      revert x y; intros (x & Hx) (y & Hy); simpl.
      unfold mb_equiv, memX; simpl; split.
      2: { intros H []; apply H. }
      intros H a; split; intros Ha.
      + assert (H1 : P a).
        { apply HP0; revert Hx; rewrite HP0; apply HA2; auto. }
        revert Ha; apply (H (exist _ a H1)).
      + assert (H1 : P a).
        { apply HP0; revert Hy; rewrite HP0; apply HA2; auto. }
        revert Ha; apply (H (exist _ a H1)).
    Qed.

    Let HP1 : finite_t (sig P).
    Proof.
      apply fin_t_finite_t.
      + intros; apply eq_bool_pirr.
      + apply finite_t_fin_t_dec; auto.
        intro; apply bool_dec.
    Qed.

    Let HA3' : forall n, In n (fol_vars B) -> P (ψ n).
    Proof. intros n Hn; apply HP0, HA3; auto. Qed.

    Let Rf s (v : vec X (ar_syms Σ s)) (x : X) :=
      mb_is_tuple_in mem (ψ (ρ s)) (proj1_sig x##vec_map (@proj1_sig _ _) v). 

    Let HA4 s : In s (fol_syms A) -> is_graph_equiv_function (Rf s) (mb_equiv memX).
    Proof.
      intros H.
      simpl in HA; do 4 apply proj2 in HA.
      apply proj1 in HA.
      rewrite fol_sem_lconj in HA.
      specialize (HA (Σ2_is_fun d (ρ s) ⟑ Σ2_is_tot (ar_syms _ s) d (ρ s))).
      rewrite fol_sem_bin_fix in HA.
      destruct HA as (F1 & F2).
      { apply in_map_iff; exists s; auto. }
      rewrite Σ2_is_fun_spec in F1.
      rewrite Σ2_is_tot_spec in F2.
      split.
      + intros v (x1 & Hx1) (x2 & Hx2) H1 H2.
        apply equivX_spec; simpl.
        unfold mem; red in F1.
        red in H1; simpl in H1.
        destruct H1 as (p & (w1 & G1 & G2) & G3).
        destruct H2 as (q & (w2 & G4 & G5) & G6).
        apply F1 with p q w1; auto.
        * apply HP0; auto.
        * apply HP0; auto.
        * generalize (mb_is_tuple_fun mem_dec HA0 _ _ _ G2 G5).
          intros; revert G4; apply mb_is_opair_congruence; auto.
      + intros v.
        specialize (F2 (vec_map (@proj1_sig _ _) v)).
        destruct F2 as (x & p & t & G1 & G2 & G3 & G4).
        * intros p; rew vec; apply HP0, (proj2_sig (vec_pos v p)).
        * unfold Rf.
          apply HP0 in G1.
          exists (exist _ x G1); simpl.
          exists p; split; simpl; auto.
          exists t; simpl; auto.
    Qed.

    Let HA4' s : In s (fol_syms A) 
             -> { f : vec X (ar_syms _ s) -> X 
                | forall v x, x = f v
                          <-> mb_is_tuple_in mem (ψ (ρ s)) (proj1_sig x##vec_map (@proj1_sig _ _) v) }.
    Proof.
      intros H.
      destruct graph_equiv_function_reif with (4 := HA4 _ H)
        as (f & Hf); auto.
      + intros; apply mb_is_tuple_in_dec; auto.
      + intros v y1 y2 ?; unfold Rf.
        intros (t & (p & H1 & H2) & H3); exists t; split; auto.
        exists p; split; auto.
        revert H1; apply mb_is_opair_congruence; auto.
        apply equivX_spec; auto.
      + exists f; intros v x.
        specialize (Hf v x).
        unfold Rf in Hf.
        rewrite Hf. 
        rewrite equivX_spec.
        split.
        * intros ->; auto.
        * generalize x (f v); clear x v Hf.
          intros (x & Hx) (y & Hy); simpl.
          rewrite Mmem; intros ->; f_equal.
          apply eq_bool_pirr.
    Qed.

    Let fn s := 
      match in_dec Hs s (fol_syms A) with
        | left Hs => proj1_sig (HA4' s Hs)
        | right _ => fun _ => exist _ _ Hx0
      end.
 
    Let Hfn s : In s (fol_syms A) 
               -> forall v x, x = fn s v
                          <-> mb_is_tuple_in mem (ψ (ρ s)) (proj1_sig x##vec_map (@proj1_sig _ _) v).
    Proof.
      intros H.
      unfold fn.
      destruct (in_dec Hs s (fol_syms A)) as [ C | [] ]; auto.
      apply (proj2_sig (HA4' s C)).
    Qed.

    Let M : fo_model Σ (sig P).
    Proof.
      exists.
      + intros s; apply (fn s).
      + intros r v.
        exact (mb_is_tuple_in mem (ψ (µ r)) (vec_map (@proj1_sig _ _) v)).
    Defined.

    Let M_dec : fo_model_dec M.
    Proof. intros r v; apply mb_is_tuple_in_dec; auto. Qed.

    Let φ n := 
      match in_dec eq_nat_dec n (fol_vars B) with
        | left H  => exist _ _ (HA3' _ H)
        | right _ => exist _ _ Hx0
      end.

    Let f : X -> Y := @proj1_sig _ _.

    Let g (y : Y) : X.
    Proof.
      refine (match mem_dec y (ψ d) with
        | left  H => exist _ y _
        | right _ => exist _ _ Hx0
      end); apply HP0, H.
    Defined.

    Let symsB : incl (fol_syms B) (fol_syms A).
    Proof.
      red; apply Forall_forall.
      apply fol_syms_subst.
      + intros; simpl; auto.
      + apply Forall_forall; auto.
    Qed.

    Let HB : fol_sem M φ B.
    Proof.
      revert HA5.
      apply Σ_Σ2_sem with (f := f) (g := g) (d := d) (φ := φ) (ψ := ψ) (F := B)
                               (ρ := ρ) (µ := µ) (MY := M2) (MX := M) (dy := ψ d); auto.
      + intros (x & Hx); apply HP0; auto.
      + intros y Hy; apply HP0 in Hy.
        exists (exist _ y Hy); auto.
      + intros (x & Hx); unfold g; simpl.
        destruct (mem_dec x (ψ d)) as [ | [] ].
        * f_equal; apply eq_bool_pirr.
        * apply HP0; auto.
      + intros i Hi; unfold φ.
        destruct (in_dec eq_nat_dec i (fol_vars B)) as [ | [] ]; auto.
      + intros s v H.
        unfold M; simpl; tauto.
    Qed.

    Local Lemma SAT2_ext_eq_to_SAT : exists X, fo_form_fin_dec_SAT_in A X.
    Proof.
      exists (sig P), M, HP1, M_dec, (fun n => φ (n+2+ns+nr)).
      revert HB; apply fol_sem_subst.
    Qed.

  End SAT2_SAT.

  Theorem SAT2_SATn : fo_form_fin_dec_SAT Σ_Σ2_enc
                   -> fo_form_fin_dec_SAT A.
  Proof.
    intros (X & M2 & H1 & H2 & psy & H3).
    assert (He : Σ2_model_ext M2) by apply H3.
    destruct (Sig2_ext_discr H1 H2 He psy _ H3) 
      as (Y & M & G1 & G2 & G3 & G4 & G5 & ψ).
    apply (SAT2_ext_eq_to_SAT G1 G2 ψ G4).
  Qed.

End Sig_Sig2_encoding.

Check SAT2_SATn.

Section SATn_SAT2.

  Variable n : nat.

  (** This is the hard implication. From a model of A, 
      build a model of Σn_Σ2_enc A in hereditary finite sets *)

  Section nested.

    Variables (A : fol_form (Σrel n))
              (X : Type) (Mn : fo_model (Σrel n) X)
              (X_fin : finite_t X)
              (X_discr : discrete X)
              (Mn_dec : fo_model_dec Mn)
              (φ : nat -> X)
              (HA : fol_sem Mn φ A).

    Let R := fom_rels Mn tt.

    Local Lemma SATn_to_SAT2 : exists Y, fo_form_fin_dec_SAT_in (@Σn_Σ2_enc n A) Y.
    Proof.
      destruct reln_hfs with (R := fom_rels Mn tt)
        as (Y & H1 & H2 & mem & H3 & l & r & i & s & H4 & H5 & H6 & H7 & H8 & H9 & H10); auto.
      exists Y, (bin_rel_Σ2 mem), H1, (bin_rel_Σ2_dec _ H3), 
        (fun n => match n with 
           | 0 => l
           | 1 => r
           | S (S n) => i (φ n)
         end).
      unfold Σn_Σ2_enc; msplit 3; auto.
      + exists (i (φ 0)); simpl; rew fot; simpl; auto.
      + apply Σ2_list_in_spec.
        intros n'; simpl.
        rewrite fol_vars_map, in_map_iff.
        intros (m & <- & ?); auto.
      + rewrite <- Σn_Σ2_correct with (Mn := Mn) (R := fun x y => y = i x) 
            (φ := fun n => match n with 0 => φ 0 | 1 => φ 1 | S (S n) => φ n end); auto.
        * rewrite fol_sem_subst.
          revert HA; apply fol_sem_ext.
          intros; simpl; rew fot; auto.
        * intros x; exists (i x); split; auto; apply H6.
        * intros v w E; rewrite H9.
          apply fol_equiv_ext; f_equal.
          apply vec_pos_ext; intro; rew vec.
        * intros n'; rewrite fol_vars_map, in_map_iff.
          intros (m & <- & Hm); simpl; auto.
    Qed.

  End nested.

  Theorem SATn_SAT2 A : fo_form_fin_discr_dec_SAT A
                     -> fo_form_fin_dec_SAT (@Σn_Σ2_enc n A).
  Proof.
    intros (X & H1 & Mn & H2 & H4 & psy & H5).
    apply SATn_to_SAT2 with X Mn psy; auto.
  Qed.

End SATn_SAT2.
