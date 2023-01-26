(* ** Discreteness *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
Import ListAutomationNotations ListAutomationHints.

From Coq Require Import Eqdep_dec.
Require Import Coq.Vectors.Vector.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
Require Import EqdepFacts.

Local Notation vec := t.

From Undecidability.FOL.Syntax Require Export Core Subst Bounded.


Local Set Implicit Arguments.
Local Unset Strict Implicit.


Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2;
                                                      [subst | try (eauto || now intros; decide equality)]
  end.

Lemma dec_vec_in X n (v : vec X n) :
  (forall x, InT x v -> forall y, dec (x = y)) -> forall v', dec (v = v').
Proof with subst; try (now left + (right; intros[=])).
  intros Hv. induction v; intros v'.
  - pattern v'. apply Vector.case0...
  - apply (Vector.caseS' v'). clear v'. intros h0 v'.
    destruct (Hv h (inl eq_refl) h0)... edestruct IHv.
    + intros x H. apply Hv. now right.
    + left. f_equal. apply e.
    + right. intros H. inversion H. resolve_existT. tauto.
Qed.

#[global]
Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
  intros v. refine (dec_vec_in _).
Qed.

Section EqDec.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.
  Hypothesis eq_dec_binop : eq_dec binop.
  Hypothesis eq_dec_quantop : eq_dec quantop.

  Global Instance dec_term : eq_dec term.
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence))
    using eq_dec_Funcs.
    intros t. induction t as [ | ]; intros [|? v']...
    - decide (x = n)... 
    - decide (F = f)... destruct (dec_vec_in X v')...
  Qed.

  Instance dec_falsity : eq_dec falsity_flag.
  Proof.
    intros b b'. unfold dec. decide equality.
  Qed.

  Lemma eq_dep_falsity b phi psi :
    eq_dep falsity_flag (form Σ_funcs Σ_preds ops) b phi b psi <-> phi = psi.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H. resolve_existT. reflexivity.
    - intros ->. reflexivity.
  Qed.

  Lemma dec_form_dep {b1 b2} phi1 phi2 : dec (eq_dep falsity_flag (@form _ _ _) b1 phi1 b2 phi2).
  Proof with subst; try (now left + (right; intros ? % eq_sigT_iff_eq_dep; resolve_existT; congruence))
    using eq_dec_Funcs eq_dec_Preds eq_dec_quantop eq_dec_binop.
    unfold dec. revert phi2; induction phi1; intros; try destruct phi2.
    all: try now right; inversion 1. now left.
    - decide (b = b0)... decide (P = P0)... decide (t = t0)... right.
      intros [=] % eq_dep_falsity. resolve_existT. tauto.
    - decide (b = b1)... decide (b0 = b2)... destruct (IHphi1_1 phi2_1).
      + apply eq_dep_falsity in e as ->. destruct (IHphi1_2 phi2_2).
        * apply eq_dep_falsity in e as ->. now left.
        * right. rewrite eq_dep_falsity in *. intros [=]. now resolve_existT.
      + right. rewrite eq_dep_falsity in *. intros [=]. now repeat resolve_existT.
    - decide (b = b0)... decide (q = q0)... destruct (IHphi1 phi2).
      + apply eq_dep_falsity in e as ->. now left.
      + right. rewrite eq_dep_falsity in *. intros [=]. now resolve_existT.
  Qed.

  Global Instance dec_form {ff : falsity_flag} : eq_dec form.
  Proof using eq_dec_Funcs eq_dec_Preds eq_dec_quantop eq_dec_binop.
    intros phi psi. destruct (dec_form_dep phi psi); rewrite eq_dep_falsity in *; firstorder.
  Qed.

  Lemma dec_full_logic_sym : eq_dec FullSyntax.full_logic_sym.
  Proof.
    cbv -[not]. decide equality.
  Qed.

  Lemma dec_full_logic_quant : eq_dec FullSyntax.full_logic_quant.
  Proof.
    cbv -[not]. decide equality.
  Qed.

  Lemma dec_frag_logic_binop : eq_dec FragmentSyntax.frag_logic_binop.
  Proof.
    cbv -[not]. decide equality.
  Qed.

  Lemma dec_frag_logic_quant : eq_dec FragmentSyntax.frag_logic_quant.
  Proof.
    cbv -[not]. decide equality.
  Qed.

  #[global] Existing Instance dec_full_logic_sym.
  #[global] Existing Instance dec_full_logic_quant.
  #[global] Existing Instance dec_frag_logic_binop.
  #[global] Existing Instance dec_frag_logic_quant.

End EqDec.



(* ** Enumerability *)

Section Enumerability.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.

  Variable list_binop : nat -> list binop.
  Hypothesis enum_binop' : list_enumerator__T list_binop binop.

  Variable list_quantop : nat -> list quantop.
  Hypothesis enum_quantop' : list_enumerator__T list_quantop quantop.

  Fixpoint vecs_from X (A : list X) (n : nat) : list (vec X n) :=
    match n with
    | 0 => [Vector.nil X]
    | S n => [ Vector.cons X x _ v | (x,  v) ∈ (A × @vecs_from X A n) ]
    end.


  Fixpoint L_term n : list term :=
    match n with
    | 0 => []
    | S n => L_term n ++ var n :: concat ([ [ func F v | v ∈ vecs_from (@L_term n) (ar_syms F) ] | F ∈ L_T n])
    end.

  Lemma L_term_cml :
    cumulative L_term.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma list_prod_in X Y (x : X * Y) A B :
    x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
  Proof.
    induction A; cbn.
    - intros [].
    - intros [H | H] % in_app_or. 2: firstorder.
      apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
  Qed.

  Lemma vecs_from_correct X (A : list X) (n : nat) (v : vec X n) :
    (forall x, InT x v -> x el A) <-> v el vecs_from A n.
  Proof.
    induction n; cbn.
    - split.
      + intros. left. pattern v. now apply Vector.case0.
      + intros [<- | []] x H. inv H.
    - split.
      + intros. revert H. apply (Vector.caseS' v).
        clear v. intros ? t0 H. in_collect (pair h t0); destruct (IHn t0).
        1: eapply H; now left.
        apply H0. intros x Hx. apply H. now right. 
      + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
        intros x H. inv H; destruct (IHn v'); eauto.
  Qed.

  Lemma vec_forall_cml X (L : nat -> list X) n (v : vec X n) :
    cumulative L -> (forall x, InT x v -> exists m, x el L m) -> exists m, v el vecs_from (L m) n.
  Proof.
    intros HL Hv. induction v; cbn.
    - exists 0. tauto.
    - destruct IHv as [m H], (Hv h) as [m' H']. 1,3:now left.
      + intros x Hx. apply Hv. now right.
      + exists (m + m'). in_collect (pair h v). 1: apply (cum_ge' (n:=m')); intuition lia.
      apply vecs_from_correct. rewrite <- vecs_from_correct in H. intros x Hx.
      apply (cum_ge' (n:=m)). all: eauto. lia.
  Qed.

  Lemma enum_term :
    list_enumerator__T L_term term.
  Proof with try (eapply cum_ge'; eauto; lia).
    intros t. induction t using term_rect.
    - exists (S x); cbn. eauto.
    - apply vec_forall_cml in H as [m H]. 2: exact L_term_cml. destruct (el_T F) as [m' H'].
      exists (S (m + m')); cbn. in_app 3. eapply in_concat. eexists. split.
      1: apply in_map_iff; exists F; split. 1: reflexivity.
      1: idtac...
      rewrite <- vecs_from_correct in H.
      eapply in_map_iff. exists v; repeat split. rewrite <- vecs_from_correct. intros x H''. specialize (H x H'')...
  Qed.

  Lemma enumT_term :
    enumerable__T term.
  Proof using enum_Funcs'.
    apply enum_enumT. exists L_term. apply enum_term.
  Qed.

  Fixpoint L_form {ff : falsity_flag} n : list form :=
    match n with
    | 0 => match ff with falsity_on => [falsity] | falsity_off => [] end
    | S n => L_form n
              ++ concat ([ [ atom P v | v ∈ vecs_from (L_term n) (ar_preds P) ] | P ∈ L_T n])
              ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (L_form n × L_form n) ] | op ∈ L_T n])
              ++ concat ([ [ quant op phi | phi ∈ L_form n ] | op ∈ L_T n])
    end.

  Lemma L_form_cml {ff : falsity_flag} :
    cumulative L_form.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma enum_form {ff : falsity_flag} :
    list_enumerator__T L_form form.
  Proof with (try eapply cum_ge'; eauto; lia).
    intros phi. induction phi.
    - exists 1. cbn; eauto.
    - rename t into v. destruct (el_T P) as [m Hm], (@vec_forall_cml term L_term _ v) as [m' Hm']; eauto using enum_term.
      exists (S (m + m')); cbn. in_app 2. eapply in_concat. eexists. split.
      1: eapply in_map_iff; exists P. 1: repeat split. 1: idtac...
      eapply in_map. rewrite <- vecs_from_correct in *. intuition...
    - destruct (el_T b0) as [m Hm], IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m + m1 + m2). cbn.
      in_app 3. apply in_concat. eexists. split. apply in_map... in_collect (pair phi1 phi2)...
    - destruct (el_T q) as [m Hm], IHphi as [m' Hm']. exists (1 + m + m'). cbn -[L_T].
      in_app 4. apply in_concat. eexists. split. apply in_map... in_collect phi...
  Qed.

  Lemma enumT_form {ff : falsity_flag} :
    enumerable__T form.
  Proof using enum_Funcs' enum_Preds' enum_binop' enum_quantop'.
    apply enum_enumT. exists L_form. apply enum_form.
  Defined.

  Definition list_enumerator_full_logic_sym (n:nat) := [FullSyntax.Conj; FullSyntax.Disj; FullSyntax.Impl].
  Lemma enum_full_logic_sym : 
    list_enumerator__T list_enumerator_full_logic_sym FullSyntax.full_logic_sym.
  Proof.
    intros [| |]; exists 0; cbn; eauto.
  Qed.
  Lemma enumT_full_logic_sym : enumerable__T FullSyntax.full_logic_sym.
  Proof.
    apply enum_enumT. eexists. apply enum_full_logic_sym.
  Qed.

  Definition list_enumerator_full_logic_quant (n:nat) := [FullSyntax.All; FullSyntax.Ex].
  Lemma enum_full_logic_quant : 
    list_enumerator__T list_enumerator_full_logic_quant FullSyntax.full_logic_quant.
  Proof.
    intros [|]; exists 0; cbn; eauto.
  Qed.
  Lemma enumT_full_logic_quant : enumerable__T FullSyntax.full_logic_quant.
  Proof.
    apply enum_enumT. eexists. apply enum_full_logic_quant.
  Qed.

  Definition list_enumerator_frag_logic_binop (n:nat) := [FragmentSyntax.Impl].
  Lemma enum_frag_logic_binop : 
    list_enumerator__T list_enumerator_frag_logic_binop FragmentSyntax.frag_logic_binop.
  Proof.
    intros []; exists 0; cbn; eauto.
  Qed.
  Lemma enumT_frag_logic_binop : enumerable__T FragmentSyntax.frag_logic_binop.
  Proof.
    apply enum_enumT. eexists. apply enum_frag_logic_binop.
  Qed.

  Definition list_enumerator_frag_logic_quant (n:nat) := [FragmentSyntax.All].
  Lemma enum_frag_logic_quant : 
    list_enumerator__T list_enumerator_frag_logic_quant FragmentSyntax.frag_logic_quant.
  Proof.
    intros []; exists 0; cbn; eauto.
  Qed.
  Lemma enumT_frag_logic_quant : enumerable__T FragmentSyntax.frag_logic_quant.
  Proof.
    apply enum_enumT. eexists. apply enum_frag_logic_quant.
  Qed.

  Theorem surj_form_ {ff:falsity_flag} (base : form):
    { Φ : nat -> form & forall y, exists x, Φ x = y }.
  Proof using enum_Funcs' enum_Preds' enum_binop' enum_quantop' list_Funcs list_Preds list_binop list_quantop.
    eexists (fun (n:nat) => match (match Cantor.of_nat n with (nn,m) => nth_error (L_form nn) m end) with Some k => k | None => base end).
    intros y.
    pose proof (list_enumerator_to_enumerator _ L_form y) as He.
    pose proof (enum_form y) as Hy.
    apply He in Hy. destruct Hy as [n Hn]. exists n.
    rewrite Hn. easy.
  Qed.

End Enumerability.

Definition enumT_form' {ff : falsity_flag} {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ops : operators} :
  enumerable__T Σ_funcs -> enumerable__T Σ_preds -> enumerable__T binop -> enumerable__T quantop -> enumerable__T form.
Proof.
  intros. apply enum_enumT.
  apply enum_enumT in H as [L1 HL1].
  apply enum_enumT in H0 as [L2 HL2].
  apply enum_enumT in H1 as [L3 HL3].
  apply enum_enumT in H2 as [L4 HL4].
  exists (L_form HL1 HL2 HL3 HL4). apply enum_form.
Qed.