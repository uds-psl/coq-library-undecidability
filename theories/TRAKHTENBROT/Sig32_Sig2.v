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
  Require Import notations fol_ops fo_terms fo_logic fo_sat membership discrete hfs rel3_hfs.

Set Implicit Arguments.

Local Notation ø := vec_nil.
Section Sig32_Sig2.

  Notation Σ2 := (Σrel 2).
  Notation Σ3 := (Σrel_eq 3).
 
  Variable (X : Type) (M2 : fo_model Σ2 X).
  Variable (Y : Type) (M3 : fo_model Σ3 Y) 
           (H3eq : fom_rels M3 false = rel2_on_vec eq).  (** The model is interpreted !! *)

  (** Can we define FO shapes and reify meta-level into FOL automagically
      like what was done for H10 ? 

      May be not very useful since the encoding is straightforward
      most of the time 
    *)

  Notation "x ∈ y" := (fol_atom Σ2 tt (£x##£y##ø)).
 
  Definition Σ2_incl x y := ∀ 0 ∈ (S x) ⤑ 0 ∈ (S y).
  Definition Σ2_equiv x y := ∀ 0 ∈ (S x) ↔ 0 ∈ (S y).

  Definition m2_member a b := fom_rels M2 tt (a##b##ø).

  Notation "x '∈m' y" := (m2_member x y) (at level 59, no associativity).

  Infix "≈" := Σ2_equiv.
  Infix "⊆" := Σ2_incl.

  Notation "⟪ A ⟫" := (fun ψ => fol_sem M2 ψ A).

  Fact Σ2_incl_spec x y ψ : ⟪Σ2_incl x y⟫ ψ = m2_incl m2_member (ψ x) (ψ y).
  Proof. reflexivity. Qed.

  Fact Σ2_equiv_spec x y ψ : ⟪Σ2_equiv x y⟫ ψ = m2_equiv m2_member (ψ x) (ψ y).
  Proof. reflexivity. Qed. 
 
  Definition Σ2_is_pair p x y : fol_form Σ2 := ∀ 0 ∈ (S p) ↔ 0 ≈ S x ⟇ 0 ≈ S y.

  Fact Σ2_is_pair_spec p x y ψ : ⟪Σ2_is_pair p x y⟫ ψ = m2_is_pair m2_member (ψ p) (ψ x) (ψ y).
  Proof. reflexivity. Qed.

  Definition Σ2_is_opair p x y := ∃∃ Σ2_is_pair 1    (2+x) (2+x)
                                   ⟑ Σ2_is_pair 0    (2+x) (2+y)
                                   ⟑ Σ2_is_pair (2+p) 1     0.

  Fact Σ2_is_opair_spec p x y ψ : ⟪Σ2_is_opair p x y⟫ ψ = m2_is_opair m2_member (ψ p) (ψ x) (ψ y).
  Proof. reflexivity. Qed.

  Definition Σ2_is_otriple p x y z := ∃ Σ2_is_opair 0     (S x) (S y)
                                      ⟑ Σ2_is_opair (S p)  0    (S z).

  Fact Σ2_is_otriple_spec p x y z ψ : ⟪Σ2_is_otriple p x y z⟫ ψ = m2_is_otriple m2_member (ψ p) (ψ x) (ψ y) (ψ z).
  Proof. reflexivity. Qed.

  Definition Σ2_is_otriple_in r x y z := ∃ Σ2_is_otriple 0 (S x) (S y) (S z) ⟑ 0 ∈ (S r).

  Fact Σ2_is_otriple_in_spec r x y z ψ : ⟪Σ2_is_otriple_in r x y z⟫ ψ = m2_is_otriple_in m2_member (ψ r) (ψ x) (ψ y) (ψ z).
  Proof. reflexivity. Qed.

  (* Terms are just variables in Σrel *)

  Definition Σ3eq_var : fo_term nat (ar_syms Σ3) -> nat.
  Proof. intros [ n | [] ]; exact n. Defined.

  (* We bound quantification inside hf-set l ∈ p and r ∈ p represent a set 
     of ordered triples corresponding to M3 *)

  Fixpoint Σ3eq_Σ2 (l r : nat) (A : fol_form Σ3) : fol_form Σ2.
  Proof.
   refine(
     match A with
      | ⊥              => ⊥
      | fol_atom _ b v => _
      | fol_bin b A B  => fol_bin b (Σ3eq_Σ2 l r A) (Σ3eq_Σ2 l r B)
      | fol_quant fol_fa A  => ∀ 0 ∈ (S l) ⤑ Σ3eq_Σ2 (S l) (S r) A
      | fol_quant fol_ex A  => ∃ 0 ∈ (S l) ⟑ Σ3eq_Σ2 (S l) (S r) A
     end).
    destruct b; simpl in v.
    + exact (Σ2_is_otriple_in r (Σ3eq_var (vec_head v)) 
                                (Σ3eq_var (vec_head (vec_tail v)))
                                (Σ3eq_var (vec_head (vec_tail (vec_tail v))))).
    + exact (Σ2_equiv (Σ3eq_var (vec_head v)) (Σ3eq_var (vec_head (vec_tail v)))).
  Defined.
  
  Notation P := (fun x y z => fom_rels M3 true (x##y##z##ø)).

  Variable R : Y -> X -> Prop.

  (** R represent a relation  M3 <~> M2 = { x | x ∈ p } which
      ensures the soundness & completeness of the encoding
      These are the conditions for correctness 

      HR1 : R is onto from M3 to { x | x ∈ l }
      HR2 : R is onto from { x | x ∈ l } to M3
      HR3 : R relates the ternary relation in M3 
            and the ternary relation <_,_,_> ∈ r in M2

    *)

  Let HR1 (l r : X) := forall y, exists x, x ∈m l /\ R y x.
  Let HR2 (l r : X) := forall x, x ∈m l -> exists y, R y x.
  Let HR3 (l r : X) := forall a b c a' b' c',
            R a a' -> R b b' -> R c c' 
         -> P a b c <-> m2_is_otriple_in m2_member r a' b' c'.
  Let HR4 := forall x y, m2_equiv m2_member x y <-> x = y.
  Let HR5 := forall x y1 y2, R y1 x -> R y2 x -> y1 = y2.
  Let HR6 := forall x1 x2 y, R y x1 -> R y x2 -> x1 = x2.

  Fact Σ2_is_otriple_in_vars r x y z : incl (fol_vars (Σ2_is_otriple_in r x y z)) (r::x::y::z::nil).
  Proof. intros a; simpl; tauto. Qed.

  Fact Σ2_is_otriple_in_equiv r x y z φ ψ :
               ⟪Σ2_is_otriple_in 3 2 1 0⟫ φ↑r↑x↑y↑z
           <-> ⟪Σ2_is_otriple_in 3 2 1 0⟫ ψ↑r↑x↑y↑z.
  Proof.
    apply fol_sem_ext.
    intros n Hn.
    apply Σ2_is_otriple_in_vars in Hn.
    revert Hn.
    repeat (intros [ <- | H ]; [ simpl; auto | revert H ]).
    simpl; tauto.
  Qed.

  Notation "⟪ A ⟫'" := (fun φ => fol_sem M3 φ A) (at level 1, format "⟪ A ⟫'").

  (* The correctness lemma *)
 
  Lemma Σ3eq_Σ2_correct (A : fol_form Σ3) l r φ ψ :
            HR1 (ψ l) (ψ r) 
         -> HR2 (ψ l) (ψ r) 
         -> HR3 (ψ l) (ψ r)
         -> HR4
         -> HR5 
         -> HR6 
        -> (forall x, In x (fol_vars A) -> R (φ x) (ψ x))
        -> ⟪ A ⟫' φ <-> ⟪Σ3eq_Σ2 l r A⟫ ψ.
  Proof.
    revert l r φ ψ.
    induction A as [ | [] | b A HA B HB | [] A HA ]; intros l r phi psy H1 H2 H3 H4 H5 H6 H.
    1: simpl; tauto.
    3: { simpl; apply fol_bin_sem_ext.
         + apply HA; intros; auto; apply H, in_or_app; simpl; auto.
         + apply HB; intros; auto; apply H, in_or_app; simpl; auto. }
    3: { simpl; split.
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
     3: { simpl; split.
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
            unfold Σ3eq_Σ2; simpl Σ3eq_var.
            red in H3.
            rewrite (@H3 _ _ _ (psy a) (psy b) (psy c)) in G1; auto.
          + unfold Σ3eq_Σ2; simpl Σ3eq_var; intros G1.
            simpl; rew fot.
            rewrite (@H3 _ _ _ (psy a) (psy b) (psy c)); auto. }
     1: { unfold Σ3eq_Σ2; rewrite Σ2_equiv_spec; simpl.
          rewrite H3eq.
          revert H; vec split v with a; vec split v with b; vec nil v; simpl.
          intros H; clear v.
          red in H4, H5, H6; rewrite H4.
          revert a b H.
          intros [ a | [] ] [ b | [] ]; simpl; intros H; rew fot.
          assert (Ha : R (phi a) (psy a)) by (apply H; auto).
          assert (Hb : R (phi b) (psy b)) by (apply H; auto).
          clear H; split.
          + intros E; rewrite <- E in Hb; apply (H6 _ _ _ Ha Hb).
          + intros E; rewrite <- E in Hb; apply (H5 _ _ _ Ha Hb). }
  Qed.

  (** The formula stating any free variable in list lv has to
      be interpreted by some element ∈ l *)

  Definition Σ2_list_in l lv := let f x A := x ∈ l ⟑ A in fold_right f (⊥⤑⊥) lv.

  Fact Σ2_list_in_spec l lv ψ : ⟪Σ2_list_in l lv⟫ ψ 
                            <-> forall x, In x lv -> ψ x ∈m ψ l.
  Proof.
    induction lv as [ | x lv IH ]; simpl.
    + split; tauto.
    + split.
      * intros (H1 & H2) ? [ <- | H ]; auto.
        apply IH; auto.
      * intros H; split.
        - apply H; auto.
        - apply IH; intros; apply H; auto.
  Qed.

  (** The FO set-theoretic axioms we need to add are minimal:
         - ∈ must be extensional (of course, this is a set-theoretic model)
         - ordered triples encoded in the usual way should exists for elements ∈ l 
         - l should not be the empty set 
         - and free variables of A (lifted twice) should be interpreted in l
   *)

  Definition Σ2_extensional := ∀∀∀ 2 ≈ 1 ⤑ 2 ∈ 0 ⤑ 1 ∈ 0.

  Fact Σ2_extensional_spec ψ : ⟪Σ2_extensional⟫ ψ = m2_member_ext m2_member.
  Proof. reflexivity. Qed.

  Definition Σ2_has_otriples l :=
    ∀∀∀ 2 ∈ (3+l) ⤑ 1 ∈ (3+l) ⤑ 0 ∈ (3+l) ⤑ ∃ Σ2_is_otriple 0 3 2 1.

  Fact Σ2_has_otriples_spec l ψ : ⟪Σ2_has_otriples l⟫ ψ = m2_has_otriples m2_member (ψ l).
  Proof. reflexivity. Qed.

  Definition Σ2_non_empty l := ∃ 0 ∈ (1+l).

  Fact Σ2_non_empty_spec l ψ : ⟪Σ2_non_empty l⟫ ψ = exists x, m2_member x (ψ l).
  Proof. reflexivity. Qed.

  Variable A : fol_form Σ3.

  (** We make some space for l and r *)

  Let B := fol_subst (fun v => £ (2+v)) A.
  Let l := 0.
  Let r := 1.

  (* Notice that Σ3_Σ2 A has two more free variables than A,
     that could be quantified existentially over if needed *)

  Definition Σ3eq_Σ2_enc := Σ2_extensional ⟑ Σ2_non_empty l
                        ⟑ Σ2_list_in l (fol_vars B) ⟑ Σ3eq_Σ2 l r B.

End Sig32_Sig2.

Section SAT2_SAT32.

  (** We show the easy implication, any model of Σ3_Σ2_enc A
     gives rise to a model of A *)

  Section nested.

    (** We start in a finite decidable discrete model where two elements 
        that cannot be distinguisged by a FO formula must be equal *)

    Variables (A : fol_form (Σrel_eq 3))
              (X : Type) 
              (M2 : fo_model (Σrel 2) X)
              (M2fin : finite_t X)
              (M2dec : fo_model_dec M2)
              (M2discr : discrete X)
              (M2bisim : forall x y, @fo_bisimilar (Σrel _) nil (tt::nil) _ M2 x y -> x = y)
              (ψ : nat -> X)
              (HA : fol_sem M2 ψ (Σ3eq_Σ2_enc A)).

    Let mem := m2_member M2.

    Let mem_dec : forall x y, { mem x y } + { ~ mem x y }.
    Proof. intros x y; apply (@M2dec tt). Qed.

    Let mem_ext a b x : m2_equiv mem a b -> mem a x -> mem b x.
    Proof. apply HA. Qed.

    (** Then by extentionality, to points/sets containing the same elements are identical
        ie we have a set-theoretic like model 

        I should move this results in a separate file !!

        Extentionality + (FO_bisim => eq) then equiv => eq 

      *)

    Let mem_equiv_bisimilar x y : m2_equiv mem x y -> x = y.
    Proof.
      unfold m2_equiv; intros Hab; apply M2bisim.
      intros B phi _ _.
      assert (Hab' : forall a, mem x a <-> mem y a).
      { intros; split; apply mem_ext; red; intro; rewrite Hab; tauto. }
      cut (forall n, (phi↑x) n = x /\ (phi↑y) n = y \/ (phi↑x) n = (phi↑y) n);
       [ | intros []; auto ].
      generalize (phi↑x) (phi↑y); clear phi.
      induction B as [ | [] v | b B HB C HC | q B HB ]; intros phi psy H; simpl; try tauto.
      + simpl in v; vec split v with a; vec split v with b; vec nil v; clear v.
        revert a b; intros [ a | [] ] [ b | [] ]; simpl; rew fot.
        change (mem (phi a) (phi b) <-> mem (psy a) (psy b)).
        destruct (H a) as [ (-> & ->) | -> ];
        destruct (H b) as [ (-> & ->) | -> ]; auto; try tauto.
        transitivity (mem x y); auto.
      + apply fol_bin_sem_ext; auto.
      + apply fol_quant_sem_ext; auto.
        intro u; apply HB.
        intros []; simpl; auto.
    Qed.
 
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

    Let M3 : fo_model (Σrel_eq 3) (sig P).
    Proof.
      exists.
      + intros [].
      + intros [] v.
        * simpl in v.
          apply (m2_is_otriple_in mem (ψ 1)).
          - exact (proj1_sig (vec_head v)).
          - exact (proj1_sig (vec_head (vec_tail v))).
          - exact (proj1_sig (vec_head (vec_tail (vec_tail v)))).
        * apply (rel2_on_vec eq v).
    Defined.

    Let M3_dec : fo_model_dec M3.
    Proof. 
      intros [] v.
      + apply m2_is_otriple_in_dec; auto. 
      + simpl.
        vec split v with a; vec split v with b; vec nil v.
        clear v; revert a b; intros (a & Ha) (b & Hb); simpl.
        destruct (M2discr a b) as [ -> | D ].
        * left; f_equal; apply UIP_dec, bool_dec.
        * right; contradict D; now inversion D.
    Qed.

    Let R (x : sig P) (y : X) := proj1_sig x = y.

    Local Lemma SAT2_to_SAT3 : exists Y, @fo_form_fin_dec_eq_SAT_in (Σrel_eq 3) false A Y.
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
      exists M3, HP1, M3_dec, eq_refl, eq_refl, (fun n => phi (2+n)).
      unfold B in *; clear B.
      rewrite <- Σ3eq_Σ2_correct with (M3 := M3) (φ := phi) (R := R) in H4.
      + rewrite fol_sem_subst in H4.
        revert H4; apply fol_sem_ext; intro; rew fot; auto.
      + auto.
      + intros (x & Hx); exists x; unfold R; simpl; split; auto.
        apply HP0 in Hx; auto.
      + intros x Hx; apply HP0 in Hx.
        exists (exist _ x Hx); red; simpl; auto.
      + intros (a & Ha) (b & Hb) (c & Hc) a' b' c'; unfold R; simpl.
        intros <- <- <-; tauto.
      + split.
        * apply mem_equiv_bisimilar.
        * intros []; red; tauto.
      + intros x (y1 & ?) (y2 & ?); unfold R; simpl; intros; subst.
        f_equal; apply UIP_dec, bool_dec.
      + intros x1 x2 (y & ?); unfold R; simpl; intros; subst; auto.
      + intros n Hn; red.
        unfold phi.
        destruct (in_dec eq_nat_dec n (fol_vars A⦃fun v : nat => in_var (2 + v)⦄))
          as [ H | [] ]; auto; simpl.
    Qed.

  End nested.

  Check SAT2_to_SAT3.

  (** We use the powerful model discretizer here *)

  Theorem SAT2_SAT32 A : fo_form_fin_dec_SAT (Σ3eq_Σ2_enc A)
                      -> @fo_form_fin_dec_eq_SAT (Σrel_eq 3) false A.
  Proof.
    intros (X & M2 & H1 & H2 & psy & H3).
    destruct (@fo_fin_model_discretize (Σrel 2) nil (tt::nil) _ H1 M2 H2)
      as (n & M & Mdec & i & j & G1 & G2 & G3 & G4 & G5).
    apply SAT2_to_SAT3 with (M2 := M) (ψ := fun n => i (psy n)); auto.
    + apply finite_t_pos.
    + red; apply pos_eq_dec.
    + revert H3.
      apply fo_model_projection 
        with (ls := nil) 
             (lr := tt::nil) 
             (i := i) (j := j); 
        auto; intros []; simpl; auto.
  Qed.

End SAT2_SAT32.

Section SAT32_SAT2.

  (** This is the hard implication. From a model of A, 
      build a model of Σ3_Σ2_enc A in hereditary finite sets *)

  Section nested.

    Variables (A : fol_form (Σrel_eq 3))
              (X : Type) (M3 : fo_model (Σrel_eq 3) X)
              (X_fin : finite_t X)
              (X_eq : fom_rels M3 false = rel2_on_vec eq)
              (M3_dec : fo_model_dec M3)
              (φ : nat -> X)
              (HA : fol_sem M3 φ A).

    Let X_discrete : discrete X.
    Proof.
      intros x y.
      change ({ rel2_on_vec eq (x##y##ø) } + { ~ rel2_on_vec eq (x##y##ø) }).
      rewrite <- X_eq.
      apply M3_dec.
    Qed.

    Let R a b c := fom_rels M3 true (a##b##c##ø).

    Local Lemma SAT3_to_SAT2 : exists Y, fo_form_fin_dec_SAT_in (Σ3eq_Σ2_enc A) Y.
    Proof.
      destruct rel3_hfs with (R := R)
        as (Y & H1 & mem & l & r & i & s & 
            H2 & _ & H3 & H4 & H5 & H6 & H7 & H8 & H9); auto.
      + apply φ, 0.
      + intros; apply M3_dec.
      + exists Y, (bin_rel_Σ2 mem), H1, (bin_rel_Σ2_dec _ H2), 
        (fun n => match n with 
           | 0 => l
           | 1 => r
           | S (S n) => i (φ n)
         end).
        unfold Σ3eq_Σ2_enc; msplit 3; auto.
        * exists (i (φ 0)); simpl; rew fot; simpl; auto.
        * apply Σ2_list_in_spec.
          intros n; simpl.
          rewrite fol_vars_map, in_map_iff.
          intros (m & <- & ?); auto.
        * rewrite <- Σ3eq_Σ2_correct with (M3 := M3) (R := fun x y => y = i x) 
            (φ := fun n => match n with 0 => φ 0 | 1 => φ 1 | S (S n) => φ n end); auto.
          - rewrite fol_sem_subst.
            revert HA; apply fol_sem_ext.
            intros; simpl; rew fot; auto.
          - intros x; exists (i x); split; auto; apply H5.
          - intros a b c ? ? ? -> -> ->; apply H8.
          - intros ? ? ? E1 E2; subst; rewrite <- H7, <- E2, H7; auto.
          - intros; subst; auto.
          - intros n; rewrite fol_vars_map, in_map_iff.
            intros (m & <- & Hm); simpl; auto.
    Qed.

  End nested.

  Theorem SAT32_SAT2 A : @fo_form_fin_dec_eq_SAT (Σrel_eq 3) false A
                       -> fo_form_fin_dec_SAT (Σ3eq_Σ2_enc A).
  Proof.
    intros (X & M3 & H2 & H4 & H5 & H6 & psy & H7).
    apply SAT3_to_SAT2 with X M3 psy; auto.
    rewrite <- H6.
    clear H6 H7 psy H4 H2.
    revert M3 H5; intros [ r s ]; simpl.
    intros E; rewrite (eq_nat_pirr E); auto.
  Qed.

End SAT32_SAT2.

Check SAT32_SAT2.
Check SAT2_SAT32.
