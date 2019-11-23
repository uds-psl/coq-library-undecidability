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
  Require Import notations fol_ops fo_terms fo_logic fo_sat membership hfs rel3_hfs.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Section Sig3_Sig2_encoding.

  Notation Σ2 := (Σrel 2).
  Notation Σ3 := (Σrel 3).

  Infix "∈" := Σ2_mem.
  Infix "≈" := Σ2_equiv.
  Infix "⊆" := Σ2_incl.

  (* We bound quantification inside hf-set l ∈ p and r ∈ p represent a set 
     of ordered triples corresponding to M3 *)

  Fixpoint Σ3_Σ2 (l r : nat) (A : fol_form Σ3) : fol_form Σ2 :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ _ v => Σ2_is_otriple_in r (Σrel_var (vec_head v)) 
                                             (Σrel_var (vec_head (vec_tail v)))
                                             (Σrel_var (vec_head (vec_tail (vec_tail v))))
      | fol_bin b A B  => fol_bin b (Σ3_Σ2 l r A) (Σ3_Σ2 l r B)
      | fol_quant fol_fa A  => ∀ 0 ∈ (S l) ⤑ Σ3_Σ2 (S l) (S r) A
      | fol_quant fol_ex A  => ∃ 0 ∈ (S l) ⟑ Σ3_Σ2 (S l) (S r) A
     end.

  Variable (X : Type) (M2 : fo_model Σ2 X).
  Variable (Y : Type) (M3 : fo_model Σ3 Y).

  (** Can we define FO shapes and reify meta-level into FOL automagically
      like what was done for H10 ? 

      May be not very useful since the encoding is straightforward
      most of the time 
    *)

  Let mem a b := fom_rels M2 tt (a##b##ø).

  Infix "∈m" := mem (at level 59, no associativity).
  Notation P := (fun x y z => fom_rels M3 tt (x##y##z##ø)).

  Variable R : Y -> X -> Prop.

  (** R represent a relation  M3 <~> M2 = { x | x ∈ p } which
      ensures the soundness & completeness of the encoding
      These are the conditions for correctness 

      HR1 : R is onto from M3 to { x | x ∈ l }
      HR2 : R is onto from { x | x ∈ l } to M3
      HR3 : R relates the ternary relation in M3 
            and the ternary relation <_,_,_> ∈ r in M2

    *)

  Let HR1 (l r : X) := forall x, exists y, y ∈m l /\ R x y.
  Let HR2 (l r : X) := forall y, y ∈m l -> exists x, R x y.
  Let HR3 (l r : X) := forall a b c a' b' c',
            R a a' -> R b b' -> R c c' 
         -> P a b c <-> mb_is_otriple_in mem r a' b' c'.

  Notation "⟪ A ⟫" := (fun ψ => fol_sem M2 ψ A).
  Notation "⟪ A ⟫'" := (fun φ => fol_sem M3 φ A) (at level 1, format "⟪ A ⟫'").

  (* The correctness lemma *)
 
  Lemma Σ3_Σ2_correct (A : fol_form Σ3) l r φ ψ :
            HR1 (ψ l) (ψ r) 
         -> HR2 (ψ l) (ψ r) 
         -> HR3 (ψ l) (ψ r)
        -> (forall x, In x (fol_vars A) -> R (φ x) (ψ x))
        -> ⟪ A ⟫' φ <-> ⟪Σ3_Σ2 l r A⟫ ψ.
  Proof.
    revert l r φ ψ.
    induction A as [ | [] | b A HA B HB | [] A HA ]; intros l r phi psy H1 H2 H4 H.
    1: simpl; tauto.
    2: { simpl; apply fol_bin_sem_ext.
         + apply HA; intros; auto; apply H, in_or_app; simpl; auto.
         + apply HB; intros; auto; apply H, in_or_app; simpl; auto. }
    2: { simpl; split.
         + intros (x & Hx).
           destruct (H1 x) as (y & G1 & G2).
           exists y; split.
           * rew fot; simpl; auto.
           * revert Hx; apply HA; auto.
             intros [ | n ]; simpl; auto.
             intros; apply H; simpl; apply in_flat_map; exists (S n); simpl; auto.
         + intros (y & G1 & G2); revert G1 G2; rew fot; simpl; intros G1 G2.
           destruct (H2 _ G1) as (x & G3).
           exists x; revert G2; apply HA; auto.
           intros [ | n ]; simpl; auto.
           intros; apply H; simpl; apply in_flat_map; exists (S n); simpl; auto. } 
  2: { simpl; split.
       + intros G1 y; rew fot; simpl; intros G2.
         destruct (H2 _ G2) as (x & G3).
         generalize (G1 x); apply HA; auto.
         intros [ | n ]; simpl; auto.
         intros; apply H; simpl; apply in_flat_map; exists (S n); simpl; auto.
       + intros G1 x.
         destruct (H1 x) as (y & G2 & G3).
         generalize (G1 _ G2); apply HA; auto.
         intros [ | n ]; simpl; auto.
         intros; apply H; simpl; apply in_flat_map; exists (S n); simpl; auto. }
  1: { revert H.
       vec split v with a; vec split v with b; vec split v with c; vec nil v; clear v.
       revert a b c; intros [ a | [] ] [ b | [] ] [ c | [] ] H; simpl in H.
       split.
       + intros G1; simpl in G1; revert G1; rew fot; intros G1.
         unfold Σ3_Σ2; simpl Σrel_var.
         red in H4.
         rewrite (@H4 _ _ _ (psy a) (psy b) (psy c)) in G1; auto.
       + unfold Σ3_Σ2; simpl Σrel_var; intros G1.
         simpl; rew fot.
         rewrite (@H4 _ _ _ (psy a) (psy b) (psy c)); auto. }
  Qed.

  Variable A : fol_form Σ3.

  (** We make some space for l and r *)

  Let B := fol_subst (fun v => £ (2+v)) A.
  Let l := 0.
  Let r := 1.

  (* Notice that Σ3_Σ2 A has two more free variables than A,
     that could be quantified existentially over if needed *)

  (** The FO set-theoretic axioms we need to add are minimal:
         - ∈ must be extensional (of course, this is a set-theoretic model)
         - ordered triples encoded in the usual way should exists for elements ∈ l 
         - l should not be the empty set 
         - and free variables of A (lifted twice) should be interpreted in l
   *)

  Definition Σ3_Σ2_enc := 
                Σ2_extensional 
              ⟑ Σ2_non_empty l
              ⟑ Σ2_list_in l (fol_vars B) 
              ⟑ Σ3_Σ2 l r B.

End Sig3_Sig2_encoding.

Section SAT2_SAT3.

  (** We show the easy implication, any model of Σ3_Σ2_enc A
     gives rise to a model of A *)

  Section nested.

    Variables (A : fol_form (Σrel 3))
              (X : Type) 
              (M2 : fo_model (Σrel 2) X)
              (M2fin : finite_t X)
              (M2dec : fo_model_dec M2)
              (ψ : nat -> X)
              (HA : fol_sem M2 ψ (Σ3_Σ2_enc A)).

    Let mem a b := fom_rels M2 tt (a##b##ø).

    Let mem_dec : forall x y, { mem x y } + { ~ mem x y }.
    Proof. intros x y; apply (@M2dec tt). Qed.

    Let P x := (if mem_dec x (ψ 0) then true else false) = true.

    Let HP0 x : P x <-> mem x (ψ 0).
    Proof.
      unfold P.
      destruct (mem_dec x (ψ 0)); split; try tauto; discriminate.
    Qed.

    Let HP1 : finite_t (sig P).
    Proof.
      apply fin_t_finite_t.
      + intros; apply UIP_dec, bool_dec.
      + apply finite_t_fin_t_dec; auto.
        intro; apply bool_dec.
    Qed.

    Let M3 : fo_model (Σrel 3) (sig P).
    Proof.
      exists.
      + intros [].
      + intros [] v.
        simpl in v.
        apply (mb_is_otriple_in mem (ψ 1)).
        * exact (proj1_sig (vec_head v)).
        * exact (proj1_sig (vec_head (vec_tail v))).
        * exact (proj1_sig (vec_head (vec_tail (vec_tail v)))).
    Defined.

    Let M3_dec : fo_model_dec M3.
    Proof. intros [] v; apply mb_is_otriple_in_dec; auto. Qed.

    Let R (x : sig P) (y : X) := proj1_sig x = y.

    Local Lemma SAT2_to_SAT3 : exists Y, fo_form_fin_dec_SAT_in A Y.
    Proof.
      exists (sig P).
      destruct HA as (H1 & H2 & H3 & H4).
      rewrite Σ2_non_empty_spec in H2.
      rewrite Σ2_list_in_spec in H3.
      revert H3 H4; set (B := A⦃fun v : nat => in_var (2 + v)⦄); intros H3 H4.
      assert (H5 : forall n, In n (fol_vars B) -> P (ψ n)).
      { intros; apply HP0, H3; auto. }
      destruct H2 as (x0 & H0).
      generalize H0; intros H2.
      apply HP0 in H0.
      set (phi := fun n : nat => 
        match in_dec eq_nat_dec n (fol_vars B) with 
          | left H  => (exist _ (ψ n) (H5 _ H) : sig P)
          | right _ => (exist _ x0 H0 : sig P)
        end).
      exists M3, HP1, M3_dec, (fun n => phi (2+n)).
      unfold B in *; clear B.
      rewrite <- Σ3_Σ2_correct with (M3 := M3) (φ := phi) (R := R) in H4.
      + rewrite fol_sem_subst in H4.
        revert H4; apply fol_sem_ext; intro; rew fot; auto.
      + intros (x & Hx); exists x; unfold R; simpl; split; auto.
        apply HP0 in Hx; auto.
      + intros x Hx; apply HP0 in Hx.
        exists (exist _ x Hx); red; simpl; auto.
      + intros (a & Ha) (b & Hb) (c & Hc) a' b' c'; unfold R; simpl.
        intros <- <- <-; tauto.
      + intros n Hn; red.
        unfold phi.
        destruct (in_dec eq_nat_dec n (fol_vars A⦃fun v : nat => in_var (2 + v)⦄))
          as [ H | [] ]; auto; simpl.
    Qed.

  End nested.

  Theorem SAT2_SAT3 A : fo_form_fin_dec_SAT (Σ3_Σ2_enc A)
                     -> fo_form_fin_dec_SAT A.
  Proof.
    intros (X & M2 & H1 & H2 & psy & H3).
    apply SAT2_to_SAT3 with X M2 psy; auto.
  Qed.

End SAT2_SAT3.

Section SAT3_SAT2.

  (** This is the hard implication. From a model of A, 
      build a model of Σ3_Σ2_enc A in hereditary finite sets *)


  Section nested.

    Variables (A : fol_form (Σrel 3))
              (X : Type) (M3 : fo_model (Σrel 3) X)
              (X_fin : finite_t X)
              (X_discr : discrete X)
              (M3_dec : fo_model_dec M3)
              (φ : nat -> X)
              (HA : fol_sem M3 φ A).

    Let R a b c := fom_rels M3 tt (a##b##c##ø).

    Local Lemma SAT3_to_SAT2 : exists Y, fo_form_fin_dec_SAT_in (Σ3_Σ2_enc A) Y.
    Proof.
      Check rel3_hfs.
      destruct rel3_hfs with (R := R)
        as (Y & H1 & H2 & mem & H3 & l & r & i & s & H4 & H5 & H6 & H7 & H8 & H9 & H10); auto.
      + apply φ, 0.
      + intros; apply M3_dec.
      + exists Y, (bin_rel_Σ2 mem), H1, (bin_rel_Σ2_dec _ H3), 
        (fun n => match n with 
           | 0 => l
           | 1 => r
           | S (S n) => i (φ n)
         end).
        unfold Σ3_Σ2_enc; msplit 3; auto.
        * exists (i (φ 0)); simpl; rew fot; simpl; auto.
        * apply Σ2_list_in_spec.
          intros n; simpl.
          rewrite fol_vars_map, in_map_iff.
          intros (m & <- & ?); auto.
        * rewrite <- Σ3_Σ2_correct with (M3 := M3) (R := fun x y => y = i x) 
            (φ := fun n => match n with 0 => φ 0 | 1 => φ 1 | S (S n) => φ n end); auto.
          - rewrite fol_sem_subst.
            revert HA; apply fol_sem_ext.
            intros; simpl; rew fot; auto.
          - intros x; exists (i x); split; auto; apply H6.
          - intros a b c ? ? ? -> -> ->; apply H9.
          - intros n; rewrite fol_vars_map, in_map_iff.
            intros (m & <- & Hm); simpl; auto.
    Qed.

  End nested.

  Theorem SAT3_SAT2 A : fo_form_fin_discr_dec_SAT A
                     -> fo_form_fin_dec_SAT (Σ3_Σ2_enc A).
  Proof.
    intros (X & H1 & M3 & H2 & H4 & psy & H5).
    apply SAT3_to_SAT2 with X M3 psy; auto.
  Qed.

End SAT3_SAT2.
