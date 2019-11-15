(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic membership.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Definition Σrel (n : nat) : fo_signature.
Proof.
  exists Empty_set unit.
  + intros [].
  + exact (fun _ => n).
Defined.

Section Sig3_Sig2.

(*  Reserved Notation "x ∈ y" (at level 59, no associativity).
  Reserved Notation "x ≈ y" (at level 59, no associativity).
  Reserved Notation "x ⊆ y" (at level 59, no associativity). *)

  Notation Σ2 := (Σrel 2).
  Notation Σ3 := (Σrel 3).
 
  Variable (X : Type) (M2 : fo_model Σ2 X).
  Variable (Y : Type) (M3 : fo_model Σ3 Y).

  Check fol_atom Σ2 tt.

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
 
  (* is_otriple t x y z := exists p, is_opair p x y /\ is_opair t p z. *)

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

  Definition Σ3_var : fo_term nat (ar_syms Σ3) -> nat.
  Proof.
    intros [ n | [] ]; exact n.
  Defined.

  Fixpoint Σ3_Σ2 (l r : nat) (A : fol_form Σ3) : fol_form Σ2 :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ _ v => Σ2_is_otriple_in r (Σ3_var (vec_head v)) 
                                             (Σ3_var (vec_head (vec_tail v)))
                                             (Σ3_var (vec_head (vec_tail (vec_tail v))))
      | fol_bin b A B  => fol_bin b (Σ3_Σ2 l r A) (Σ3_Σ2 l r B)
      | fol_quant fol_fa A  => ∀ 0 ∈ (S l) ⤑ Σ3_Σ2 (S l) (S r) A
      | fol_quant fol_ex A  => ∃ 0 ∈ (S l) ⟑ Σ3_Σ2 (S l) (S r) A
     end.

  Notation P := (fun x y z => fom_rels M3 tt (x##y##z##ø)).

  Variable R : Y -> X -> Prop.

  (** R represent for M3 = { x | x in l } and M2 the relation 

           fun x y => proj1_sig x ≈ y  *)

  Definition HR1 (l r : X) := forall x, exists y, fom_rels M2 tt (y##l##ø) /\ R x y.
  Definition HR2 (l r : X) := forall y, fom_rels M2 tt (y##l##ø) -> exists x, R x y.
  Definition HR4 (l r : X) := forall a b c a' b' c',
                                               R a a'
                                            -> R b b'
                                            -> R c c' 
                                            -> fom_rels M3 tt (a##b##c##ø)
                                           <-> m2_is_otriple_in m2_member r a' b' c'.

  (** Notice the following in HR4, the value of ψ is arbitrary *)

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

  Theorem Σ3_Σ2_correct (A : fol_form Σ3) l r φ ψ :
            HR1 (ψ l) (ψ r) -> HR2 (ψ l) (ψ r) -> HR4 (ψ l) (ψ r)
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
         unfold Σ3_Σ2; simpl Σ3_var.
         red in H4.
         rewrite (@H4 _ _ _ (psy a) (psy b) (psy c)) in G1; auto.
       + unfold Σ3_Σ2; simpl Σ3_var; intros G1.
         simpl; rew fot.
         rewrite (@H4 _ _ _ (psy a) (psy b) (psy c)); auto. }
  Qed.

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

  Let B := fol_subst (fun v => £ (2+v)) A.
  Let l := 0.
  Let r := 1.

  Definition Σ3_Σ2_enc := Σ2_extensional ⟑ Σ2_non_empty l
                        ⟑ Σ2_list_in l (fol_vars B) ⟑ Σ3_Σ2 l r B.

End Sig3_Sig2.

Definition SAT Σ (A : fol_form Σ) := exists X (M : fo_model Σ X) φ, fol_sem M φ A.

Section SAT2_SAT3.

  Section nested.

    Variables (A : fol_form (Σrel 3))
              (X : Type) (M2 : fo_model (Σrel 2) X)
              (ψ : nat -> X)
              (HA : fol_sem M2 ψ (Σ3_Σ2_enc A)).

    Let mem := m2_member M2.

    (** Beware that model is NOT finite ... unless one assumes more *)

    Let M3 : fo_model (Σrel 3) (sig (fun x => mem x (ψ 0))).
    Proof.
      exists.
      + intros [].
      + intros [] v.
        simpl in v.
        apply (m2_is_otriple_in mem (ψ 1)).
        * exact (proj1_sig (vec_head v)).
        * exact (proj1_sig (vec_head (vec_tail v))).
        * exact (proj1_sig (vec_head (vec_tail (vec_tail v)))).
    Defined.

    Let R (x : {x | mem x (ψ 0)}) (y : X) := proj1_sig x = y.

    Local Lemma SAT2_to_SAT3 : SAT A.
    Proof.
      destruct HA as (H1 & H2 & H3 & H4).
      rewrite Σ2_non_empty_spec in H2.
      rewrite Σ2_list_in_spec in H3.
      destruct H2 as (x0 & H0).
      set (phi := fun n : nat => 
        match in_dec eq_nat_dec n (fol_vars A⦃fun v : nat => in_var (2 + v)⦄) with 
          | left H  => (exist _ (ψ n) (H3 _ H) : {x | mem x (ψ 0)})
          | right _ => (exist _ x0 H0 : {x | mem x (ψ 0)})
        end).
      exists {x | mem x (ψ 0)}, M3, (fun n => phi (2+n)).
      rewrite <- Σ3_Σ2_correct with (φ := phi) (R := R) in H4.
      + rewrite fol_sem_subst in H4.
        revert H4; apply fol_sem_ext; intro; rew fot; auto.
      + intros (x & Hx); exists x; unfold R; simpl; split; auto.
      + intros x Hx; exists (exist _ x Hx); red; simpl; auto.
      + intros (a & Ha) (b & Hb) (c & Hc) a' b' c'; unfold R; simpl.
        intros <- <- <-; tauto.
      + intros n Hn; red.
        unfold phi.
        destruct (in_dec eq_nat_dec n (fol_vars A⦃fun v : nat => in_var (2 + v)⦄))
          as [ H | [] ]; auto; simpl.
    Qed.

  End nested.

  Theorem SAT2_SAT3 A : SAT (Σ3_Σ2_enc A) -> SAT A.
  Proof.
    intros (X & M2 & psy & HA).
    apply SAT2_to_SAT3 with X M2 psy; auto.
  Qed.

End SAT2_SAT3.

Section SAT3_SAT2.
 
  Section nested.

    Variables (A : fol_form (Σrel 3))
              (X : Type) (M3 : fo_model (Σrel 3) X)
              (M3_fin : finite_t X)
              (M3_dec : fo_model_dec M3)
              (φ : nat -> X)
              (HA : fol_sem M3 φ A).

    (** we need to build a map pos n -> set *)

  End nested.

End SAT3_SAT2.
    


  

  


Check SAT2_SAT3.
