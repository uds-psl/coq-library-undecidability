(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Max Bool.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts
                 InformativeDefinitions InformativeReducibilityFacts.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite fin_quotient fin_dec utils_decidable.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable
                 fol_ops fo_sig fo_terms fo_logic
                 fo_sat fo_sat_dec

                 red_utils 
                 Sig1 Sig1_1 Sig0 red_dec.

Set Implicit Arguments.

Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊑" := incl (at level 70, no associativity). 
Local Notation ø := vec_nil.

Section discernable.

  Variable (X : Type).

  Definition discernable x y := exists f : X -> bool, f x <> f y.

  Fact discernable_equiv1 x y : discernable x y <-> exists f, f x = true /\ f y = false.
  Proof.
    split.
    + intros (f & Hf).
      case_eq (f x); intros Hx.
      * exists f; split; auto.
        now rewrite Hx in Hf; destruct (f y).
      * exists (fun x => negb (f x)).
        rewrite Hx in *; split; auto.
        now destruct (f y).
    + intros (f & E1 & E2); exists f.
      now rewrite E1, E2.
  Qed.

  Definition undiscernable x y := forall f : X -> bool, f x = f y.

  Fact discernable_undiscernable x y : discernable x y -> undiscernable x y -> False.
  Proof. intros (f & Hf) H; apply Hf, H. Qed.

  Fact undiscernable_spec x y : undiscernable x y <-> ~ discernable x y.
  Proof.
    split.
    + intros H1 H2; revert H2 H1; apply discernable_undiscernable.
    + intros H f.
      destruct (bool_dec (f x) (f y)); auto.
      destruct H; exists f; auto.
  Qed.

  Fact undiscernable_refl x : undiscernable x x.
  Proof. red; auto. Qed.

  Fact undiscernable_sym x y : undiscernable x y -> undiscernable y x.
  Proof. red; auto. Qed.

  Fact undiscernable_trans x y z : undiscernable x y -> undiscernable y z -> undiscernable x z.
  Proof. unfold undiscernable; eauto. Qed.

  Fact undiscernable_discrete D (f : X -> D) x y : discrete D -> undiscernable x y -> f x = f y.
  Proof.
    intros d H.
    set (g z := if d (f x) (f z) then true else false).
    specialize (H g); unfold g in H.
    destruct (d (f x) (f x)) as [ _ | [] ]; auto.
    destruct (d (f x) (f y)) as [ | ]; auto.
  Qed.

  Fact discrete_undiscernable_implies_equal x y : discrete X -> undiscernable x y -> x = y.
  Proof. intro; now apply undiscernable_discrete with (f := fun x => x). Qed.

  Fact undiscernable_Prop_dec x y : undiscernable x y -> forall P, (forall x, decidable (P x)) -> P x <-> P y.
  Proof.
    intros H P HP.
    set (f x := if HP x then true else false).
    specialize (H f); unfold f in H.
    destruct (HP x); destruct (HP y); try tauto; easy.
  Qed.

  Hypothesis (H2 : forall x y, decidable (discernable x y)).

  Let H3 x y : decidable (undiscernable x y).
  Proof.
    destruct (H2 x y); [ right | left ]; rewrite undiscernable_spec; tauto.
  Qed.

  Definition discriminable_list l := 
    { D & { _ : discrete D & { _ : finite_t D & { f : X -> D 
             | forall x y, In x l -> In y l -> undiscernable x y <-> f x = f y } } } }.

  Hint Resolve undiscernable_refl undiscernable_sym undiscernable_trans : core.

  Theorem discernable_discriminable_list l : discriminable_list l. 
  Proof.
    apply DEC_PER_list_proj_finite_discrete with (l := l) (R := undiscernable).
    + split; eauto.
    + red; apply H3.
    + intros; auto.
  Qed.

  Definition discriminable_type := 
    { D & { _ : discrete D & { _ : finite_t D & { f : X -> D 
             | forall x y, undiscernable x y <-> f x = f y } } } }.

  Hypothesis (H1 : finite_t X).

  (* undiscernable is equivalent to a equality after mapping on some finite datatype *)

  Theorem finite_discernable_discriminable_type : discriminable_type. 
  Proof.
    destruct H1 as (l & Hl).
    destruct discernable_discriminable_list with l
      as (D & D1 & D2 & f & Hf).
    exists D, D1, D2, f; intros; eauto.
  Qed.

End discernable.

Section FSAT_equiv_discernable_rels.

  Variable Σ : fo_signature.

  Local Definition test K := @fol_atom Σ K (vec_set_pos (fun _ => £0)).

  Variables (P Q : rels Σ).

  Section model.

    Variable (f : rels Σ -> bool) (HP : f P = true) (HQ : f Q = false).

    Let M : fo_model Σ bool.
    Proof.
      split.
      + intros; exact true. 
      + intros r _; exact (f r = true).
    Defined.

    Local Fact discernable_rels_FSAT : FSAT Σ (test P ⟑ (test Q ⤑ ⊥)).
    Proof.
      exists bool, M; msplit 2.
      + apply finite_t_bool.
      + intros r v; simpl; apply bool_dec.
      + exists (fun _ => true); simpl.
        now rewrite HP, HQ.
    Qed.

  End model.

  Theorem FSAT_equiv_discernable_rels : 
            FSAT Σ (test P ⟑ (test Q ⤑ ⊥))
        <-> discernable P Q.
  Proof.
    rewrite discernable_equiv1.
    split.
    + intros (D & M & H1 & H2 & rho & H3 & H4).
      exists (fun K => if @H2 K (vec_set_pos (fun _ => rho 0)) then true else false).
      simpl in H3, H4 |- *.
      rewrite vec_map_set_pos in H3, H4.
      do 2 match goal with 
        |- context[if ?c then _ else _] => destruct c 
      end; auto; tauto.
    + intros (f & H1 & H2).
      apply discernable_rels_FSAT with f; auto.
  Qed.

End FSAT_equiv_discernable_rels.

Section FSAT_equiv_discernable_syms.
  
  Variables (Σ : fo_signature) (P : rels Σ) (HP : ar_rels Σ P = 1).

  Let termt (p : syms Σ) : fo_term (ar_syms Σ) := in_fot p (vec_set_pos (fun _ => in_var 0)).

  Local Definition testt (p : syms Σ) : fol_form Σ := fol_atom P (cast (termt p##ø) (eq_sym HP)).

  Variables (p q : syms Σ).

  Section model.

    Variable (f : syms Σ -> bool) (Hp : f p = true) (Hq : f q = false).

    Let M : fo_model Σ bool.
    Proof.
      split.
      + intros s _; exact (f s). 
      + intros r; simpl; intros v. 
        exact (match v with vec_nil => True | h##_ => h = true end).
    Defined.

    Local Fact discernable_syms_FSAT : FSAT Σ (testt p ⟑ (testt q ⤑ ⊥)).
    Proof.
      exists bool, M; msplit 2.
      + apply finite_t_bool.
      + intros r v; simpl.
        destruct v; try tauto.
        apply bool_dec.
      + exists (fun _ => true); simpl.
        rewrite HP; simpl.
        now rewrite Hp, Hq.
    Qed.

  End model.

  Theorem FSAT_equiv_discernable_syms : 
            FSAT Σ (testt p ⟑ (testt q ⤑ ⊥))
        <-> discernable p q.
  Proof.
    rewrite discernable_equiv1.
    split.
    + intros (D & M & H1 & H2 & rho & H3 & H4).
      simpl in H3, H4 |- *.
      exists (fun k => if H2 P (vec_map (fo_term_sem M rho)
          (cast (termt k ## ø) (eq_sym HP))) then true else false).
      do 2 match goal with 
        |- context[if ?c then _ else _] => destruct c 
      end; auto; tauto.
    + intros (f & H1 & H2).
      apply discernable_syms_FSAT with f; auto.
  Qed.

End FSAT_equiv_discernable_syms.

Section FSAT_DEC_implies_discernable_rels.

  (* For any signature, FSAT decidability implies 
     decidable discernability of rels *)

  Variable Σ : fo_signature.

  Hypothesis HXY : forall A, decidable (FSAT Σ A).

  Theorem FSAT_dec_implies_discernable_rels_dec (P Q : rels Σ) : decidable (discernable P Q).
  Proof.
    destruct (HXY (test _ P ⟑ (test _ Q ⤑ ⊥))) as [ H | H ].
    + left; revert H; apply FSAT_equiv_discernable_rels.
    + right; contradict H; revert H; apply FSAT_equiv_discernable_rels.
  Qed.

End FSAT_DEC_implies_discernable_rels.

Section FSAT_DEC_implies_discernable_syms.

  (* For any signature with a unary relation, 
     FSAT decidability implies decidable discernability of syms *)

  Variables (Σ : fo_signature) (P : rels Σ) (HP : ar_rels Σ P = 1).

  Hypothesis HXY : forall A, decidable (FSAT Σ A).

  Theorem FSAT_dec_implies_discernable_syms_dec (f g : syms Σ) : decidable (discernable f g).
  Proof.
    destruct (HXY (testt _ _ HP f ⟑ (testt _ _ HP g ⤑ ⊥))) as [ H | H ].
    + left; revert H; apply FSAT_equiv_discernable_syms.
    + right; contradict H; revert H; apply FSAT_equiv_discernable_syms.
  Qed.

End FSAT_DEC_implies_discernable_syms.

Section discrete_projection.

  Variable (X Y : Type) (HY : discrete Y) (f : X -> Y) (l : list X).

  Fact find_discrete_projection y : { x | x ∊ l /\ f x = y } + (forall x, x ∊ l -> f x <> y).
  Proof.
    destruct list_choose_dep 
      with (P := fun x => f x = y) (Q := fun x => f x <> y) (l := l)
    as [ (? & ? & ?) | ]; eauto.
    intros; apply HY.
  Qed.

End discrete_projection.

Section discriminable_implies_FSAT_DEC.

  Variable (X Y : Type) 
           (lX : list X) (HlX : discriminable_list lX)
           (lY : list Y) (HlY : discriminable_list lY).

  Let DX := projT1 HlX.

  Let DX_discr : discrete DX.   Proof. apply (projT2 HlX). Qed.
  Let DX_fin : finite_t DX.     Proof. apply (projT2 (projT2 HlX)). Qed.

  Let f : X -> DX := proj1_sig (projT2 (projT2 (projT2 HlX))).
  Let Hf u v : u ∊ lX -> v ∊ lX -> undiscernable u v <-> f u = f v.
  Proof. apply (proj2_sig (projT2 (projT2 (projT2 HlX)))). Qed.

  Let DY := projT1 HlY.

  Let DY_discr : discrete DY.   Proof. apply (projT2 HlY). Qed.
  Let DY_fin : finite_t DY.     Proof. apply (projT2 (projT2 HlY)). Qed.

  Let g : Y -> DY := proj1_sig (projT2 (projT2 (projT2 HlY))).
  Let Hg u v : u ∊ lY -> v ∊ lY -> undiscernable u v <-> g u = g v.
  Proof. apply (proj2_sig (projT2 (projT2 (projT2 HlY)))). Qed.

  Let fromX d : { x | x ∊ lX /\ f x = d } + (forall x, x ∊ lX -> f x <> d).
  Proof. now apply find_discrete_projection. Qed.

  Let fromY d : { y | y ∊ lY /\ g y = d } + (forall y, y ∊ lY -> g y <> d).
  Proof. now apply find_discrete_projection. Qed.

  Fixpoint fot_discriminable_discrete (t : fo_term (fun _ : X => 1)) : fo_term (fun _ : DX => 1) :=
    match t with
      | in_var n => in_var n
      | in_fot s v => in_fot (f s) ((fot_discriminable_discrete (vec_pos v pos0))##ø)
    end.

  Fixpoint Σdiscriminable_discrete (A : fol_form (Σ11 X Y)) : fol_form (Σ11 DX DY) :=
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => @fol_atom (Σ11 DX DY) (g r) (vec_map fot_discriminable_discrete v)
      | fol_bin b A B => fol_bin b (Σdiscriminable_discrete A) (Σdiscriminable_discrete B)
      | fol_quant q A => fol_quant q (Σdiscriminable_discrete A)
    end.

  Section sound.

    Variable (K : Type).

    Variable (M : fo_model (Σ11 X Y) K) (HM : fo_model_dec M) (Kdiscr : discrete K).

    Let M' : fo_model (Σ11 DX DY) K.
    Proof.
      split.
      + intros s.
        destruct (fromX s) as [ (x & Hx1 & Hx2) | C ].
        * apply (fom_syms M x).
        * apply vec_head.
      + intros r.
        destruct (fromY r) as [ (y & Hy1 & Hy2) | C ].
        * apply (fom_rels M y).
        * exact (fun _ => True).
    Defined.

    Let M'_dec : fo_model_dec M'.
    Proof.
      intros r v; simpl.
      destruct (fromY r) as [ (y & Hy1 & Hy2) | C ].
      + apply HM.
      + tauto.
    Qed.

    Let term_equal (t : fo_term (fun _ : X => 1)) φ : 
             fo_term_syms t ⊑ lX
          -> fo_term_sem M' φ (fot_discriminable_discrete t)
           = fo_term_sem M φ t.
    Proof.
      induction t as [ n | s v IH ]; simpl; intros Ht; auto.
      destruct (fromX (f s)) as [ (x & Hx1 & Hx2) | C ].
      2: destruct (C s); auto.
      revert IH Ht; vec split v with a; vec nil v; intros IH Ht.
      simpl in Ht |- *.
      rewrite <- app_nil_end in Ht.
      specialize (IH pos0); simpl in IH.
      assert (undiscernable x s) as Hxs by (apply Hf; auto).
      rewrite IH.
      2: apply incl_tran with (2 := Ht); intro; simpl; tauto.
      apply undiscernable_discrete with (f := fun u => fom_syms M u (fo_term_sem M φ a ## ø)); auto.
    Qed.

    Let form_equiv (A : fol_form (Σ11 X Y)) φ :
          fol_syms A ⊑ lX
       -> fol_rels A ⊑ lY
       -> fol_sem M' φ (Σdiscriminable_discrete A) <-> fol_sem M φ A.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in φ |- *; simpl; intros G1 G2; try tauto. 
      + destruct (fromY (g r)) as [ (y & Hy1 & Hy2) | C ].
        2: destruct (C r); auto.
        apply Hg in Hy2; auto.
        apply undiscernable_Prop_dec 
          with (P := fun z => fom_rels M z (vec_map (fo_term_sem M φ) v)) in Hy2.
        2: intro; apply HM.
        rewrite <- Hy2.
        fol equiv.
        rewrite vec_map_map.
        clear Hy2.
        revert G1; vec split v with a; vec nil v; simpl; rewrite <- app_nil_end; intros G1.
        f_equal; apply term_equal; auto.
      + apply fol_bin_sem_ext; auto.
        * eapply HA, incl_tran; eauto.
        * eapply HB, incl_tran; eauto.
      + destruct q; fol equiv; auto.
    Qed.

    Hypothesis Kfin : finite_t K.
    Variables (φ : nat -> K) 
              (A : fol_form (Σ11 X Y))
              (HA1 : fol_syms A ⊑ lX) 
              (HA2 : fol_rels A ⊑ lY)
              (HA : fol_sem M φ A).

    Local Fact Σdiscriminable_discrete_sound : FSAT _ (Σdiscriminable_discrete A).
    Proof.
      exists K, M', Kfin, M'_dec, φ.
      now apply form_equiv.
    Qed.

  End sound.

  Section complete.

    Variable (K : Type).

    Variable (M : fo_model (Σ11 DX DY) K) (HM : fo_model_dec M).

    Let M' : fo_model (Σ11 X Y) K.
    Proof.
      split.
      + exact (fun s => fom_syms M (f s)).
      + exact (fun r => fom_rels M (g r)).
    Defined.

    Let M'_dec : fo_model_dec M'.
    Proof.
      intros r v; simpl.
      apply HM.
    Qed.

    Let term_equal t φ : fo_term_sem M φ (fot_discriminable_discrete t)
                       = fo_term_sem M' φ t.
    Proof.
      induction t as [ n | s v IH ]; simpl; auto.
      specialize (IH pos0); revert IH.
      vec split v with a; vec nil v; simpl; intros ->; auto.
    Qed.

    Let form_equiv A φ : fol_sem M φ (Σdiscriminable_discrete A) <-> fol_sem M' φ A.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in φ |- *; simpl; try tauto.
      + rewrite vec_map_map; fol equiv.
        vec split v with a; vec nil v; simpl; f_equal; auto.
      + apply fol_bin_sem_ext; auto.
      + destruct q; fol equiv; auto.
    Qed.

    Hypothesis Kfin : finite_t K.
    Variables (φ : nat -> K) (A : fol_form (Σ11 X Y)) (HA : fol_sem M φ (Σdiscriminable_discrete A)).

    Local Fact Σdiscriminable_discrete_complete : FSAT _ A.
    Proof.
      exists K, M', Kfin, M'_dec, φ.
      now apply form_equiv.
    Qed.

  End complete.

  Theorem Σdiscriminable_discrete_correct (A : fol_form (Σ11 X Y)) :
          fol_syms A ⊑ lX
       -> fol_rels A ⊑ lY
       -> { DX : _ & 
          { DY : _ & 
          { _ : discrete DX &
          { _ : discrete DY & 
          { _ : finite_t DX &
          { _ : finite_t DY &
          { B : fol_form (Σ11 DX DY) | FSAT _ A <-> FSAT _ B } } } } } } }. 
  Proof.
    intros HX HY.
    exists DX, DY.
    do 4 (exists; [ auto | ]).
    exists (Σdiscriminable_discrete A).
    split.
    + rewrite fo_form_fin_dec_SAT_discr_equiv.
      intros (K & H0 & M & H1 & H2 & phi & H3).
      apply Σdiscriminable_discrete_sound with K M phi; auto.
    + intros (K & M & H1 & H2 & phi & H3).
      apply Σdiscriminable_discrete_complete with K M phi; auto.
  Qed.

End discriminable_implies_FSAT_DEC.

Theorem Σdiscernable_dec_to_discrete X Y :
           (forall u v : X, decidable (discernable u v))
        -> (forall u v : Y, decidable (discernable u v))
        -> forall A : fol_form (Σ11 X Y), 
           { DX : _ 
         & { DY : _ 
         & { _ : discrete DX
         & { _ : discrete DY
         & { _ : finite_t DX
         & { _ : finite_t DY
         & { B | FSAT (Σ11 X Y) A <-> FSAT (Σ11 DX DY)  B } } } } } } }.
Proof.
  intros HX HY A.
  generalize (discernable_discriminable_list HX (fol_syms A))
             (discernable_discriminable_list HY (fol_rels A)); intros HlX HlY.
  destruct (Σdiscriminable_discrete_correct HlX HlY A)
    as (DX & DY & ? & ? & ? & ? & B & HB).
  1,2: apply incl_refl.
  exists DX, DY.
  do 4 (exists; [ auto | ]).
  exists B; auto.
Qed.

Theorem Σ11_discernable_dec_FSAT X Y : 
          (forall u v : X, decidable (discernable u v))
       -> (forall u v : Y, decidable (discernable u v))
       -> forall A, decidable (FSAT (Σ11 X Y) A).
Proof.
  intros H0 H1 A.
  destruct (Σdiscernable_dec_to_discrete H0 H1 A) 
    as (DX & DY & ? & ? & ? & ? & B & HB); auto.
  destruct FSAT_FULL_MONADIC_DEC with (A := B); simpl; auto.
  + left; tauto.
  + right; tauto.
Qed. 

Section FSAT_FULL_MONADIC_discernable.

  Variable (Σ : fo_signature) 
           (H1 : forall u v : syms Σ, decidable (discernable u v))
           (H2 : forall u v : rels Σ, decidable (discernable u v))
           (H3 : forall s, ar_syms Σ s <= 1)
           (H4 : forall r, ar_rels Σ r <= 1).

  Theorem FSAT_FULL_MONADIC_discernable A : decidable (FSAT Σ A).
  Proof.
    destruct (FSAT_FULL_MONADIC_FSAT_11 _ H3 H4) as (f & Hf).
    destruct (Σ11_discernable_dec_FSAT H1 H2 (f A)) as [ H | H ].
    + left; apply Hf; auto.
    + right; contradict H; apply Hf; auto.
  Qed.

End FSAT_FULL_MONADIC_discernable.

Section FSAT_PROP_ONLY_discernable.

  Variable (Σ : fo_signature)
           (H1 : forall u v : rels Σ, decidable (discernable u v))
           (H2 : forall r, ar_rels Σ r = 0).

  Theorem FSAT_PROP_ONLY_discernable A : decidable (FSAT Σ A).
  Proof.
    destruct (FSAT_PROP_FSAT_x0 _ H2) as (f & Hf).
    destruct FSAT_FULL_MONADIC_discernable with (A := f A)
      as [ H | H ]; auto.
    + intros [].
    + left; revert H; apply Hf; auto.
    + right; contradict H; revert H; apply Hf; auto.
  Qed.

End FSAT_PROP_ONLY_discernable.

Theorem FULL_MONADIC_discernable (Σ : fo_signature) :
          { _ : forall u v : syms Σ, decidable (discernable u v) &
          { _ : forall u v : rels Σ, decidable (discernable u v)
              | (forall s, ar_syms Σ s <= 1)
             /\ (forall r, ar_rels Σ r <= 1) } }
        + { _ : forall u v : rels Σ, decidable (discernable u v)
              | forall r, ar_rels Σ r = 0 }
       -> forall A, decidable (FSAT Σ A).
Proof.
  intros [ (H1 & H2 & H3 & H4) | (H1 & H2) ].
  + apply FSAT_FULL_MONADIC_discernable; auto.
  + apply FSAT_PROP_ONLY_discernable; auto.
Qed.

(* For a monadic signature Σ (arity 0 or 1) with at least one unary relation,

   FSAT is decidable iff both syms and rels have decidable discernability 
*)

Theorem FULL_MONADIC_discernable_dec_FSAT_dec_equiv Σ r : 
            ar_rels Σ r = 1 
         -> (forall s, ar_syms Σ s <= 1)
         -> (forall r, ar_rels Σ r <= 1)
         -> ( (forall u v : syms Σ, decidable (discernable u v))
            * (forall u v : rels Σ, decidable (discernable u v)) )
          ≋ forall A, decidable (FSAT Σ A).
Proof.
  intros Hr H1 H2.
  split.
  + intros (? & ?); apply FSAT_FULL_MONADIC_discernable; auto.
  + intros H3; split.
    * apply FSAT_dec_implies_discernable_syms_dec with r; auto.
    * apply FSAT_dec_implies_discernable_rels_dec; auto.
Qed.

(* For a signature with only constant relations (arity 0),
   FSAT is decidable iff relations have decidable discernability *) 

Theorem MONADIC_PROP_discernable_dec_FSAT_dec_equiv (Σ : fo_signature) :
            (forall r, @ar_rels Σ r = 0)
        ->  (forall u v : rels Σ, decidable (discernable u v))
          ≋  forall A, decidable (FSAT Σ A).
Proof.
  intros H; split.
  + intros; apply FULL_MONADIC_discernable; eauto.
  + intros H1.
    assert (forall A, decidable (FSAT (Σ0 Σ) A)) as H2.
    { revert H1; apply ireduction_decidable, FSAT_x0_FSAT_PROP; auto. }
    exact (FSAT_dec_implies_discernable_rels_dec H2).
Qed. 

