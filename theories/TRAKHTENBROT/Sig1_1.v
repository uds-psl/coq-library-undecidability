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
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat Sig_no_syms.

Import fol_notations.

Set Implicit Arguments.

Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊑" := incl (at level 70, no associativity). 

(* * Removal of function symbols from full monadic signatures *)

Fixpoint find_non_empty_word X (l : list (list X)) : 
           { s & { w | s::w ∊ l } } 
         + { concat l = nil }.
Proof.
  destruct l as [ | [ | s w ] l ].
  + right; auto.
  + destruct (find_non_empty_word X l) as [ (s & w & H) | H ].
    * left; exists s, w; right; auto.
    * right; simpl; auto.
  + left; exists s, w; left; auto.
Qed.

Local Notation ø := vec_nil.

Section fot_word_var.

  (* when arity of symbols is 1, terms have the shape s1(s2(...sn(i)...)) 
     where [s1,...,sn] is a list of symbols and i is a variable *)

  Variable (X : Type).

  Implicit Type t : fo_term (fun _ : X => 1).

  Fixpoint fot_var t :=
    match t with
      | in_var i   => i
      | in_fot s v => fot_var (vec_pos v pos0)
    end.

  Fixpoint fot_word t :=
    match t with
      | in_var i   => nil
      | in_fot s v => s::fot_word (vec_pos v pos0)
    end.

  Fixpoint fot_word_var w i : fo_term (fun _ : X => 1) :=
    match w with
      | nil  => in_var i
      | s::w => in_fot s (fot_word_var w i##ø)
    end.

  Fact fot_word_var_eq t : t = fot_word_var (fot_word t) (fot_var t).
  Proof.
    induction t as [ | s v IH ]; simpl in *; auto; f_equal.
    generalize (IH pos0); clear IH; vec split v with t; vec nil v; clear v; simpl.
    intros; f_equal; auto.
  Qed.

  Fact fot_word_eq w i : fot_word (fot_word_var w i) = w.
  Proof. induction w; simpl; f_equal; auto. Qed.

  Fact fot_var_eq w i : fot_var (fot_word_var w i) = i.
  Proof. induction w; simpl; f_equal; auto. Qed.

End fot_word_var.

Section Σ11_words.

  Variable (X Y : Type).

  (* Signatures with arity always 1 for both syms and rels *)

  Definition Σ11 : fo_signature.
  Proof.
    exists X Y; intros _.
    + exact 1.
    + exact 1.
  Defined.

  Fixpoint Σ11_words (A : fol_form Σ11) : list (list X) :=
    match A with 
      | ⊥              => nil
      | fol_atom r v   => (fot_word (vec_pos v pos0))::nil
      | fol_bin _ A B  => Σ11_words A++Σ11_words B
      | fol_quant _ A  => Σ11_words A
    end.

End Σ11_words.

Section Σfull_mon_rem.

  (* The proof of Proposition 6.2.7 (Gradel) of pp 251 in
        "The Classical Decision Problem" 

     cannot be impleted as is. The individual step is ok 
     but the induction does not work because 
          SAT (A /\ C) <-> SAT (B /\ C) 
     is NOT implied by SAT A <-> SAT B !! 

     At least I do not see how the implement the iterative
     process in a sound way ... termination is OK but
     invariants pose problems
  *)

  (* Hence we do the conversion in a single pass !! *)

  Variable (Y : Type) (HY : finite_t Y)
           (n m : nat).

  Notation X := (pos n).

  (* Bounded lists *)

  Let Yw := { w : list X | length w < S m }.

  Let YwY_fin : finite_t (Yw*Y).
  Proof. 
    apply finite_t_prod; auto. 
    apply finite_t_list, finite_t_pos.
  Qed.

  Let lwY := proj1_sig YwY_fin.
  Let HlwY p : p ∊ lwY.
  Proof. apply (proj2_sig YwY_fin). Qed.

  (* The new signature is not finite (list X !!)
      but this of no impact on decidability. However,
      the signature is discrete, if Y is discrete *)

  Notation Σ := (Σ11 X Y).
  Notation Σ' := (Σ11 X (list X*Y + Y)).

  Let f s v := @in_fot _ (ar_syms Σ') s v##ø.
  Let P r v : fol_form Σ' := @fol_atom Σ' (inr r) v.
  Let Q w r v : fol_form Σ' :=  @fol_atom Σ' (inl (w,r)) v.

  Arguments f : clear implicits.
  Arguments P : clear implicits.
  Arguments Q : clear implicits.

  (* An atomic formula of Σ as the form r(s1(...(sn(x))))
     and we encode it as the monadic Q_([sn;...;s1],r) (x) 

     To ensure correctness, we have to add the non-simply 
     monadic equations:
     
                  P_r x <-> Q_(nil,r) x 
         and Q_(s::w,r) <-> Q_(w,r) (s x)

     In these, there is still Q_* (s x) which is not
     simply monodic. Later, we skolemize those equations
     to get rid of the compound term (s x)

     Notice that we have to bound n above to ensure that 
     those equations are finitely many
   *)

  Local Fixpoint encode (A : fol_form Σ) : fol_form Σ' :=
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => 
        let t := vec_head v in
        let w := fot_word t in
        let x := fot_var  t 
        in  Q (rev w) r (£x##ø)
      | fol_bin b A B => fol_bin b (encode A) (encode B)
      | fol_quant q A => fol_quant q (encode A)
    end.

  Notation Σfull_mon_rec := encode.

  (* The reduction function does not map to a signature void of
     functions to simplify the above expression. However, the
     obtained formula is void of any function symbols *)

  Fact Σfull_mon_rec_syms A : fol_syms (Σfull_mon_rec A) = nil.
  Proof.
    induction A as [ | r v | b A HA B HB | q A HA ].
    1,2,4: simpl; tauto.
    simpl; rewrite HA, HB; auto.
  Qed.

  Variable (A : fol_form Σ) (HwA : forall w, w ∊ Σ11_words A -> length w < S m).

  (* Equations P_r (£0) <-> Q_(nil,r) (£0) 
           and Q_(s::w,r) (£0) <-> Q_(w,r) (s(£0)) *)

  Let Eq (p : Yw * Y) : fol_form Σ' :=
    let v := £0##ø in 
    let (w,r) := p in
    let (w,_) := w in
    match w with
      | nil   => Q nil r v ↔ P r v
      | s::w' => Q w' r (f s v) ↔ Q w r v
    end.

  (* The previous equations but skolemized by s(£0) <-> £(s) *) 

  Let Eq' (p : Yw * Y) := 
    let m := £n##ø  in
    let (w,r) := p  in
    let (w,_) := w  in
    match w with
      | nil   => Q nil r m ↔ P r m
      | s::w' => Q w' r (£(pos2nat s)##ø) ↔ Q w r m
    end.

  (* We first deals with the non-skolemized reduction *)

  Definition Σfull_mon_red : fol_form Σ' :=
    Σfull_mon_rec A ⟑ ∀ fol_lconj (map Eq lwY).

  Variable (K : Type).

  (* Interpretation of a list of functions mapped on a value *)

  Let Fixpoint g (M : fo_model Σ K) w x :=
    match w with
      | nil  => x
      | s::w => g M w (fom_syms M s (x##ø))
    end.

  Let g_app M w1 w2 x : g M (w1++w2) x = g M w2 (g M w1 x).
  Proof. revert x; induction w1; simpl; auto. Qed.

  Let g_snoc M w s x : g M (w++s::nil) x = fom_syms M s (g M w x##ø).
  Proof. rewrite g_app; auto. Qed.

  Section soundness.

    Variable (M : fo_model Σ K).

    Let M' : fo_model Σ' K.
    Proof.
      split.
      + exact (fom_syms M).
      + intros [ (w,r) | r ]; simpl in r |- *.
        * exact (fun v  => fom_rels M r (g M w (vec_head v)##ø)).
        * exact (fom_rels M r).
    Defined.

    Fact Σfull_mon_rec_sound φ : 
         fol_sem M' φ (Σfull_mon_rec A) <-> fol_sem M φ A.
    Proof.
      revert φ HwA; induction A as [ | r v | b B HB C HC | q B HB ]; intros φ HA.
      + simpl; tauto.
      + simpl in v; unfold Σfull_mon_rec.
        revert HA; vec split v with t; vec nil v; clear v; simpl vec_head; simpl syms; intros HA.
        specialize (HA _ (or_introl eq_refl)); simpl in HA |- *.
        replace (fo_term_sem M φ t) 
        with    (fo_term_sem M φ (fot_word_var (fot_word t) (fot_var t))).
        * simpl; apply fol_equiv_ext; do 2 f_equal.
          generalize (fot_word t) (fot_var t); clear t HA; intros w.
          induction w as [ | s w IHw ]; simpl; auto; intros i.
          rewrite g_snoc; simpl; do 2 f_equal; auto.
        * f_equal; symmetry; apply fot_word_var_eq.
      + simpl; apply fol_bin_sem_ext.
        * apply HB; intros ? ?; apply HA, in_app_iff; auto.
        * apply HC; intros ? ?; apply HA, in_app_iff; auto.
      + simpl; apply fol_quant_sem_ext; intro; apply HB; auto.
    Qed.

    Variable (Kfin : finite_t K)
             (Mdec : fo_model_dec M)
             (φ : nat -> K)
             (HA : fol_sem M φ A).

    Theorem Σfull_mon_rem_sound : fo_form_fin_dec_SAT_in Σfull_mon_red K.
    Proof.
      exists M', Kfin.
      exists.
      { intros [ (w,r) | r ]; simpl in r |- *; intro; apply Mdec. } 
      exists φ; simpl; split.
      + apply Σfull_mon_rec_sound; auto.
      + intro x; rewrite fol_sem_lconj.
        intros ?; rewrite in_map_iff.
        intros ((([|s w]&Hw),r) & <- & Hr); unfold Eq.
        * simpl; auto.
        * simpl; auto.
    Qed.

  End soundness.

  Section completeness.

    Variable (M' : fo_model Σ' K).

    Let M : fo_model Σ K.
    Proof.
      split.
      + exact (fom_syms M').
      + exact (fun r => fom_rels M' (inr r)).
    Defined.

    Section Σfull_mon_rec_complete.

      Hypothesis HM1' : forall s w r x, length (s::w) < S m 
                                 -> fom_rels M' (inl (s::w, r)) (x##ø)
                                <-> fom_rels M' (inl (w, r)) (fom_syms M s (x##ø)##ø).
 
      Hypothesis HM2' : forall r x, fom_rels M' (inr r) (x##ø)
                                <-> fom_rels M' (inl (nil,r)) (x##ø).

      Let Hf φ w i : g M (rev w) (φ i) = fo_term_sem M φ (fot_word_var w i).
      Proof.
        induction w; simpl; auto.
        rewrite g_snoc; simpl in *; rewrite IHw; auto.
      Qed.

      Fact Σfull_mon_rec_complete φ : 
        fol_sem M' φ (Σfull_mon_rec A) <-> fol_sem M φ A.
      Proof.
        revert φ HwA; induction A as [ | r v | b B HB C HC | q B HB ]; intros φ HwA.
        + simpl; tauto.
        + simpl in v; unfold Σfull_mon_rec.
          revert HwA; vec split v with t; vec nil v; clear v; simpl vec_head; simpl syms; intros HwA.
          specialize (HwA _ (or_introl eq_refl)); simpl in HwA |- *.
          replace (fo_term_sem M φ t) 
          with    (fo_term_sem M φ (fot_word_var (fot_word t) (fot_var t))).
          * revert HwA; generalize (fot_word t) (fot_var t); intros w i.
            rewrite <- (rev_length w), <- Hf. 
            simpl; generalize (rev w) (φ i); clear w; intros w.
            induction w as [ | s w IHw ]; simpl; auto; intros Hw x.
            - rewrite HM2'; tauto.
            - rewrite HM1', IHw; simpl; try tauto; lia.
          * f_equal; symmetry; apply fot_word_var_eq.
        + apply fol_bin_sem_ext.
          * apply HB; intros ? ?; apply HwA, in_app_iff; auto.
          * apply HC; intros ? ?; apply HwA, in_app_iff; auto.
        + simpl; apply fol_quant_sem_ext; intro; apply HB; auto.
      Qed.

    End Σfull_mon_rec_complete.

    Variable (Kfin : finite_t K)
             (M'dec : fo_model_dec M')
             (φ : nat -> K)
             (HA : fol_sem M' φ Σfull_mon_red).

    Theorem Σfull_mon_rem_complete : fo_form_fin_dec_SAT_in A K.
    Proof.
      exists M, Kfin.
      exists.
      { intros r'; simpl in r'; intros v; apply M'dec. }
      exists φ; simpl.
      simpl in HA. destruct HA as [ H1 H2 ].
      revert H1; apply Σfull_mon_rec_complete.
      + intros s w r x Hw.
        simpl in H2; specialize (H2 x).
        rewrite fol_sem_lconj in H2.
        symmetry; apply (H2 (Eq (exist _ (s::w) Hw,r))), in_map_iff.
        exists (exist _ (s::w) Hw,r); split; auto.
      + intros r x.
        simpl in H2; specialize (H2 x).
        rewrite fol_sem_lconj in H2.
        symmetry; apply (H2 (Eq (exist _ nil (lt_0_Sn _),r))), in_map_iff.
        exists (exist _ nil (lt_0_Sn _),r); split; auto.
    Qed.

  End completeness.

  (* The non-skolemized reduction is correct *)

  Theorem Σfull_mon_red_correct : fo_form_fin_dec_SAT_in A K 
                              <-> fo_form_fin_dec_SAT_in Σfull_mon_red K.
  Proof.
    split.
    + intros (M & H1 & H2 & phi & H3).
      apply Σfull_mon_rem_sound with M phi; auto.
    + intros (M' & H1 & H2 & phi & H3).
      apply Σfull_mon_rem_complete with M' phi; auto.
  Qed.

  (* Now we skolemize the right part (equations) and show correctness *)

  Definition Σfull_mon_red' : fol_form Σ' :=
    Σfull_mon_rec A ⟑ ∀ fol_mquant fol_ex n (fol_lconj (map Eq' lwY)).

  Local Lemma Σfull_mon_red'_sound : 
          fo_form_fin_dec_SAT_in Σfull_mon_red K
       -> fo_form_fin_dec_SAT_in Σfull_mon_red' K.
  Proof.
    intros (M & Kfin & Mdec & φ & H1 & H2); simpl in H1, H2.
    exists M, Kfin, Mdec, φ; simpl; split; auto.
    intros x; specialize (H2 x).
    rewrite fol_sem_mexists.
    exists (vec_set_pos (fun p => fom_syms M p (x##ø))).
    rewrite fol_sem_lconj; intros ?; rewrite in_map_iff.
    intros (c & <- & H).
    rewrite fol_sem_lconj in H2.
    specialize (H2 (Eq c) (in_map _ _ _ H)).
    clear H; revert H2.
    destruct c as (([ | s w ],?),r); simpl.
    + rewrite env_vlift_fix1 with (k := 0); simpl; auto.
    + rewrite env_vlift_fix1 with (k := 0).
      rewrite env_vlift_fix0; simpl; rew vec.
  Qed.

  Section Σfull_mon_red'_complete.

    Variable (M : fo_model Σ' K)
             (Kfin : finite_t K)
             (Mdec : fo_model_dec M)
             (φ : nat -> K)
             (HA : fol_sem M φ Σfull_mon_red').

    Let R x (v : vec _ n) := fol_sem M (env_vlift x·φ v) (fol_lconj (map Eq' lwY)).

    Let Rreif : { r : K -> vec K n | forall x, R x (r x) }.
    Proof.
      apply finite_t_dec_choice.
      + apply finite_t_vec; auto.
      + intros x v; apply fol_sem_dec; auto.
      + simpl in HA; apply proj2 in HA.
        intros x; generalize (HA x).
        rewrite fol_sem_mexists; auto.
    Qed.

    Let r := proj1_sig Rreif.
    Let Hg x : fol_sem M (env_vlift x·φ (r x)) (fol_lconj (map Eq' lwY)).
    Proof. apply (proj2_sig Rreif). Qed.

    Let M' : fo_model Σ' K.
    Proof.
      split.
      + simpl; intros p v.
        exact (vec_pos (r (vec_head v)) p).
      + exact (fom_rels M).
    Defined.

    Local Lemma Σfull_mon_red'_complete : fo_form_fin_dec_SAT_in Σfull_mon_red K.
    Proof.
      exists M', Kfin, Mdec, φ.
      simpl; split.
      + simpl in HA; generalize (proj1 HA).
        apply fo_model_nosyms.
        * apply Σfull_mon_rec_syms.
        * intros; simpl; tauto.
      + intros x.
        specialize (Hg x).
        rewrite fol_sem_lconj in Hg.
        rewrite fol_sem_lconj.
        intros u; rewrite in_map_iff.
        intros (c & <- & Hc).
        specialize (Hg (Eq' c) (in_map _ _ _ Hc)).
        revert Hg.
        destruct c as (([|s w]&?),?); simpl.
        * rewrite env_vlift_fix1 with (k := 0); simpl; auto.
        * rewrite env_vlift_fix1 with (k := 0).
          rewrite env_vlift_fix0; simpl; rew vec.
    Qed.

  End Σfull_mon_red'_complete.

  (* The non-skolemized reduction is correct *)

  Theorem Σfull_mon_red'_correct : 
          fo_form_fin_dec_SAT_in A K
      <-> fo_form_fin_dec_SAT_in Σfull_mon_red' K.
  Proof.
    rewrite Σfull_mon_red_correct. 
    split.
    + apply Σfull_mon_red'_sound.
    + intros (M & H1 & H2 & phi & H3). 
      apply Σfull_mon_red'_complete with M phi; auto.
  Qed.

  (* And produce a syms-free formula *)

  Theorem Σfull_mon_red'_no_syms : fol_syms Σfull_mon_red' = nil.
  Proof.
    cut (incl (fol_syms Σfull_mon_red') nil).
    + generalize (fol_syms Σfull_mon_red').
      intros [ | x l ] H; auto.
      destruct (H x); simpl; auto.
    + simpl.
      rewrite Σfull_mon_rec_syms, fol_syms_mquant.
      rewrite fol_syms_bigop, <- app_nil_end; simpl.
      intros x; rewrite in_flat_map.
      intros (u & H & Hu); revert H.
      rewrite in_map_iff.
      intros (c & <- & Hc).
      revert Hu.
      destruct c as (([|s w]&?),r); simpl; auto.
  Qed.

End Σfull_mon_rem.

Section Σ11_reduction.

  (* We can lower the hypotheses now by computing m from A *)

  Variable (n : nat) (Y : Type) (HY : finite_t Y) (A : fol_form (Σ11 (pos n) Y)) (K : Type).

  Local Definition max_depth := lmax (map (@length _) (Σ11_words A)).

  Notation m := max_depth.

  Let Hmd w : w ∊ Σ11_words A -> length w < S m.
  Proof.
    intros Hw; apply le_n_S, lmax_prop, in_map_iff.
    exists w; auto.
  Qed.

  Definition Σ11_red := Σfull_mon_red' HY m A.

  Theorem Σ11_red_correct : fo_form_fin_dec_SAT_in A K <-> fo_form_fin_dec_SAT_in Σ11_red K.
  Proof. apply Σfull_mon_red'_correct; auto. Qed.

  Theorem Σ11_red_no_syms : fol_syms Σ11_red = nil.
  Proof. apply Σfull_mon_red'_no_syms. Qed.

End Σ11_reduction.

(* We get the elimination of symbols *)

Section Σ11_Σ1.

  Variable (n : nat) (P : Type) (HY : finite_t P) (A : fol_form (Σ11 (pos n) P)).

  Theorem Σ11_Σ1_reduction : { B : fol_form (Σ11 Empty_set (list (pos n)*P + P)) 
                                 | fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT B }.
  Proof.
    destruct Σ_no_sym_correct with (A := Σ11_red HY A) as (B & HB).
    { rewrite Σ11_red_no_syms; apply incl_refl. }
    exists B; rewrite <- HB; split; intros (X & H); exists X; revert H; apply Σ11_red_correct.
  Qed.

End Σ11_Σ1.


