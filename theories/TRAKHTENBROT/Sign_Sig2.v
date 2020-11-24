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
  Require Import notations decidable fol_ops fo_sig fo_terms fo_logic fo_sat
                 membership hfs reln_hfs.

Set Implicit Arguments.

(* * From Σ=(ø;{R^n}) to Σ=(ø;{R^2}) *)

Local Notation ø := vec_nil.

Section Sign_Sig2_encoding.

  Variable (n : nat).

  Notation Σ2 := (Σrel 2).
  Notation Σn := (Σrel n).

  Infix "∈" := Σ2_mem.
  Infix "≈" := Σ2_equiv.
  Infix "⊆" := Σ2_incl.

  (* We bound quantification inside hf-set l ∈ p and r ∈ p represent a set 
     of ordered triples corresponding to M3 *)

  Fixpoint Σn_Σ2 (d r : nat) (A : fol_form Σn) : fol_form Σ2 :=
    match A with
      | ⊥             => ⊥
      | fol_atom _  v => Σ2_is_tuple_in r (vec_map (@Σrel_var _) v)
      | fol_bin b A B => fol_bin b (Σn_Σ2 d r A) (Σn_Σ2 d r B)
      | fol_quant fol_fa A  => ∀ 0 ∈ (S d) ⤑ Σn_Σ2 (S d) (S r) A
      | fol_quant fol_ex A  => ∃ 0 ∈ (S d) ⟑ Σn_Σ2 (S d) (S r) A
     end.

  Variable (X : Type) (M2 : fo_model Σ2 X).
  Variable (Y : Type) (Mn : fo_model Σn Y).

  Let mem a b := fom_rels M2 tt (a##b##ø).

  Infix "∈m" := mem (at level 59, no associativity).
  Notation P := (fun v => fom_rels Mn tt v).

  Variable R : Y -> X -> Prop.

  (* R represent a relation  Mn <~> M2 = { x | x ∈ p } which
      ensures the soundness & completeness of the encoding
      These are the conditions for correctness 

      HR1 : R is onto from Mn to { x | x ∈ l }
      HR2 : R is onto from { x | x ∈ l } to Mn
      HR3 : R relates the n-ary relation in Mn 
            and the n-ary relation <_,...,_> ∈ r in M2

    *)

  Let HR1 (d r : X) := forall y, exists x, x ∈m d /\ R y x.
  Let HR2 (d r : X) := forall x, x ∈m d -> exists y, R y x.
  Let HR3 (d r : X) := forall v w, (forall p, R (vec_pos v p) (vec_pos w p))
         -> P v <-> mb_is_tuple_in mem r w.

  Notation "⟪ A ⟫" := (fun ψ => fol_sem M2 ψ A).
  Notation "⟪ A ⟫'" := (fun φ => fol_sem Mn φ A) (at level 1, format "⟪ A ⟫'").

  (* The correctness lemma *)
 
  Lemma Σn_Σ2_correct (A : fol_form Σn) d r φ ψ :
            HR1 (ψ d) (ψ r) 
         -> HR2 (ψ d) (ψ r) 
         -> HR3 (ψ d) (ψ r)
        -> (forall x, In x (fol_vars A) -> R (φ x) (ψ x))
        -> ⟪ A ⟫' φ <-> ⟪Σn_Σ2 d r A⟫ ψ.
  Proof.
    revert d r φ ψ.
    induction A as [ | [] v | b A HA B HB | [] A HA ]; intros l r phi psy H1 H2 H3 H.
    + simpl; tauto.
    + simpl; red in H3.
      rewrite H3 with (w := vec_map (fun x => psy (Σrel_var x)) v).
      * apply (fol_quant_sem_ext fol_ex); intros x.
        apply (fol_bin_sem_ext fol_conj); try tauto.
        rewrite Σ2_is_tuple_spec; simpl.
        rewrite !vec_map_map; simpl; tauto.
      * intros p; rewrite !vec_pos_map.
        case_eq (vec_pos v p).
        2: intros [].
        simpl; intros x Hx; rewrite Hx; simpl.
        apply H; simpl; apply in_flat_map.
        exists (vec_pos v p); split.
        - apply in_vec_list, in_vec_pos.
        - simpl; rewrite Hx; simpl; auto.
    + simpl; apply fol_bin_sem_ext; [ apply HA | apply HB ];
        intros; auto; apply H, in_or_app; simpl; auto.
    + simpl; split.
      * intros (x & Hx).
        destruct (H1 x) as (y & G1 & G2).
        exists y; split.
        - rew fot; simpl; auto.
        - revert Hx; apply HA; auto.
          intros [ | n' ]; simpl; auto.
          intros; apply H; simpl; apply in_flat_map; exists (S n'); simpl; auto.
      * intros (y & G1 & G2); revert G1 G2; rew fot; simpl; intros G1 G2.
        destruct (H2 _ G1) as (x & G3).
        exists x; revert G2; apply HA; auto.
        intros [ | n' ]; simpl; auto.
        intros; apply H; simpl; apply in_flat_map; exists (S n'); simpl; auto.
    + simpl; split.
      * intros G1 y; rew fot; simpl; intros G2.
        destruct (H2 _ G2) as (x & G3).
        generalize (G1 x); apply HA; auto.
        intros [ | n' ]; simpl; auto.
        intros; apply H; simpl; apply in_flat_map; exists (S n'); simpl; auto.
      * intros G1 x.
        destruct (H1 x) as (y & G2 & G3).
        generalize (G1 _ G2); apply HA; auto.
        intros [ | n' ]; simpl; auto.
        intros; apply H; simpl; apply in_flat_map; exists (S n'); simpl; auto.
  Qed.

  Variable A : fol_form Σn.

  (* We make some space for l and r *)

  Let B := fol_subst (fun v => £ (2+v)) A.
  Let d := 0.
  Let r := 1.

  (* Notice that Σn_Σ2 A has two more free variables than A,
     that could be quantified existentially over if needed *)

  (* The FO set-theoretic axioms we need to add are somewhat minimal:
         - ∈ must be extensional (of course, this is a set-theoretic model)
         - ordered n-tuples encoded in the usual way should exists for elements ∈ l 
         - l should not be the empty set 
         - and free variables of A (lifted twice) should be interpreted in l
   *)

  Definition Σn_Σ2_enc := 
                Σ2_extensional 
              ⟑ Σ2_non_empty d
              ⟑ Σ2_list_in d (fol_vars B) 
              ⟑ Σn_Σ2 d r B.

End Sign_Sig2_encoding.

Section SAT2_SATn.

  Variable n : nat.

  (* We show the easy implication, any model of Σn_Σ2_enc A
     gives rise to a model of A *)

  Section nested.

    Variables (A : fol_form (Σrel n))
              (X : Type) 
              (M2 : fo_model (Σrel 2) X)
              (M2fin : finite_t X)
              (M2dec : fo_model_dec M2)
              (ψ : nat -> X)
              (HA : fol_sem M2 ψ (Σn_Σ2_enc A)).

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

    Let Mn : fo_model (Σrel n) (sig P).
    Proof.
      exists.
      + intros [].
      + intros [] v.
        simpl in v.
        apply (@mb_is_tuple_in _ mem (ψ 1) n).
        apply (vec_map (@proj1_sig _ _) v).
    Defined.

    Let Mn_dec : fo_model_dec Mn.
    Proof. intros [] v; apply mb_is_tuple_in_dec; auto. Qed.

    Let R (x : sig P) (y : X) := proj1_sig x = y.

    Local Lemma SAT2_to_SATn : exists Y, fo_form_fin_dec_SAT_in A Y.
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
      exists Mn, HP1, Mn_dec, (fun n => phi (2+n)).
      unfold B in *; clear B.
      rewrite <- Σn_Σ2_correct with (Mn := Mn) (φ := phi) (R := R) in H4.
      + rewrite fol_sem_subst in H4.
        revert H4; apply fol_sem_ext; intro; rew fot; auto.
      + intros (x & Hx); exists x; unfold R; simpl; split; auto.
        apply HP0 in Hx; auto.
      + intros x Hx; apply HP0 in Hx.
        exists (exist _ x Hx); red; simpl; auto.
      + intros v w Hvw. simpl.
        apply fol_equiv_ext; f_equal.
        apply vec_pos_ext; intros p.
        rewrite vec_pos_map; apply Hvw.
      + intros j Hj; red.
        unfold phi.
        destruct (in_dec eq_nat_dec j (fol_vars A⦃fun v : nat => in_var (2 + v)⦄))
          as [ H | [] ]; auto; simpl.
    Qed.

  End nested.

  Theorem SAT2_SATn A : fo_form_fin_dec_SAT (@Σn_Σ2_enc n A)
                     -> fo_form_fin_dec_SAT A.
  Proof.
    intros (X & M2 & H1 & H2 & psy & H3).
    apply SAT2_to_SATn with X M2 psy; auto.
  Qed.

End SAT2_SATn.

Section SATn_SAT2.

  Variable n : nat.

  (* This is the hard implication. From a model of A, 
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
