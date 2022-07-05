(** ** Normal Sequent Calculus **)

From Undecidability Require Import Shared.ListAutomation.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
Import ListAutomationNotations.
From Undecidability Require Import FOL.Syntax.Facts.
From Undecidability Require Import FOL.Syntax.Theories.
From Undecidability.FOL.Deduction Require Export FragmentSequent FragmentNDFacts.
From Undecidability.FOL.Semantics.Kripke Require Import FragmentCore FragmentSoundness.
Import FragmentSyntax.
Export FragmentSyntax.

Section Gentzen.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma seq_consistent :
    ~ [] ⊢S ⊥.
  Proof.
    enough (forall ff (H : falsity_on = ff), ~ [] ⊢S (match H in _ = f return @form _ _ _ f with eq_refl _ => ⊥ end)) as H.
    - apply (H falsity_on eq_refl).
    - intros ff Heq. remember nil. remember None.
      remember (match _ with eq_refl _ => _ end).
      intros H. induction H; subst; try intuition congruence.
      now eapply IHsprv with eq_refl.
  Qed.

  Section Weakening.
    Context {b : falsity_flag}.

    Lemma seq_Weak A B phi psi :
      sprv A phi psi -> A <<= B -> sprv B phi psi.
    Proof.
      intros H; induction H in B |-*; intuition; eauto using incl_map. 
    Qed.

    Theorem seq_subst_Weak A phi psi sigma :
      sprv A phi psi -> sprv ([phi[sigma] | phi ∈ A]) (option_map (subst_form sigma) phi) psi[sigma].
    Proof.
      induction 1 in sigma |-*; cbn; eauto using in_map.
      - apply AllR. setoid_rewrite map_map in IHsprv. erewrite map_map, map_ext.
        apply IHsprv. intros ?. cbn. now rewrite up_form.
      - specialize (IHsprv sigma). apply AllL with (t := t`[sigma]). cbn in IHsprv.
        rewrite subst_comp in *. unfold scons, funcomp in *. erewrite subst_ext. apply IHsprv.
        intros [|n]. 1: easy. cbn. unfold funcomp. rewrite subst_term_comp. apply subst_term_id.
        easy.
    Qed.

    Context {HdF : eq_dec Σ_funcs} {HdP : eq_dec Σ_preds}.

    Lemma seq_nameless_equiv_all' A phi n :
      bounded_L n A -> bounded (S n) phi -> [f[↑] | f ∈ A] ⊢S phi <-> A ⊢S phi[$n..].
    Proof.
      intros HL Hphi. split.
      - intros H. apply (seq_subst_Weak ($n..)) in H. rewrite map_map in *.
        erewrite map_ext, map_id in H; try apply H. intros. apply subst_shift.
      - intros H. apply (seq_subst_Weak (cycle_shift n)) in H.
        rewrite (map_ext_in _ (subst_form ↑)) in H.
        + now rewrite cycle_shift_subject in H.
        + intros psi HP. now apply cycle_shift_shift, HL.
    Qed.
  End Weakening.

  (* **** Normalization *)
  Local Unset Implicit Arguments.
  (* We redefine sprv and prv in Type so we define predicates on them. *)
  Inductive tsprv : forall (b : falsity_flag), list form -> option form -> form -> Type :=
  | TContr {b} A phi psi : tsprv b A (Some phi) psi -> phi el A -> tsprv b A None psi
  | TIR {b} A phi psi : tsprv b (phi :: A) None psi -> tsprv b A None (phi → psi)
  | TAllR {b} A phi : tsprv b (map (subst_form ↑) A) None phi -> tsprv b A None (∀ phi)
  | TAbsurd A phi : tsprv falsity_on A None ⊥ -> tsprv falsity_on A None phi
  | TAx {b} A phi : tsprv b A (Some phi) phi
  | TIL {b} A phi psi xi : tsprv b A None phi -> tsprv b A (Some psi) xi -> tsprv b A (Some (phi → psi)) xi
  | TAllL {b} A phi t psi : tsprv b A (Some (phi[t..])) psi -> tsprv b A (Some (∀ phi)) psi.
  Arguments tsprv {_} _ _ _.

  Inductive tprv : forall (b : falsity_flag), list (form) -> form -> Type :=
  | TII {b} A phi psi : tprv b (phi::A) psi -> tprv b A (phi → psi)
  | TIE {b} A phi psi : tprv b A (phi → psi) -> tprv b A phi -> tprv b A psi
  | TAllI {b} A phi : tprv b (map (subst_form ↑) A) phi -> tprv b A (∀ phi)
  | TAllE {b} A t phi : tprv b A (∀ phi) -> tprv b A (phi [t..])
  | TExp A phi : tprv falsity_on A ⊥ -> tprv falsity_on A phi
  | TCtx {b} A phi : phi el A -> tprv b A phi.
  Arguments tprv {_} _ _.

  Definition not_II {b : falsity_flag} {A} {phi} (p : tprv A phi) : Prop :=
    match p with
    | (TII _ _ _ p') => False
    | (TAllI _ _ p') => True
    | (TAllE _ _ _ p') => True
    | (TExp _ _ p') => True
    | (TIE _ _ _ p' p'') => True
    | (TCtx _ _ _) => True
    end.

  Definition not_AllI {b : falsity_flag} {A} {phi} (p : tprv A phi) : Prop :=
    match p with
    | (TII _ _ _ p') => True
    | (TAllI _ _ p') => False
    | (TAllE _ _ _ p') => True
    | (TExp _ _ p') => True
    | (TIE _ _ _ p' p'') => True
    | (TCtx _ _ _) => True
    end.

  Fixpoint normal {b : falsity_flag} {A} {phi} (p : tprv A phi) : Prop :=
    match p with
    | (TII _ _ _ p') => normal p'
    | (TIE _ _ _ p' p'') => normal p' /\ normal p'' /\ not_II p'
    | (TAllI _ _ p') => normal p'
    | (TAllE _ _ _ p') => normal p' /\ not_AllI p'
    | (TExp _ _ p') => normal p'
    | (TCtx _ _ _) => True
    end.

  Section CutElimination.
    Context {b : falsity_flag}.

    Definition embed A phi psi :=
      match phi with
      | Some phi' => @prv _ _ _ intu A phi' -> @prv _ _ _ intu A psi
      | None => @prv _ _ _ intu A psi
      end.

    Lemma seq_ND A phi psi :
      sprv A phi psi -> embed A phi psi.
    Proof.
      unfold embed; induction 1; cbn in *.
      - refine (IHsprv (Ctx H0)).
      - refine (II IHsprv).
      - refine (AllI IHsprv).
      - refine (Exp phi IHsprv).
      - tauto.
      - intros. refine (IHsprv2 (IE H1 IHsprv1)).
      - intros. refine (IHsprv (AllE t H0)).
    Qed.

    Lemma seq_ND_T T phi :
      stprv T phi -> @FragmentND.tprv _ _ b intu T phi.
    Proof.
      intros (A & HA1 & HA2). apply seq_ND in HA2. now use_theory A.
    Qed.

    Definition tembed A phi psi :=
      match phi with
      | Some phi' => forall (p : tprv A phi'), not_AllI p /\ not_II p /\ normal p -> exists (p' : tprv A psi), normal p'
      | None => exists (p : tprv A psi), normal p
      end.

    Lemma cutfree_seq_ND A phi psi :
      tsprv A phi psi -> tembed A phi psi.
    Proof with try split; cbn in *; unfold not_II, not_AllI in *; try tauto.
      unfold tembed; induction 1; cbn in *.
      - apply (IHX (TCtx _ _ i))...
      - destruct IHX. exists (TII _ _ _ x)...
      - destruct IHX. exists (TAllI _ _ x)...
      - destruct IHX. exists (TExp _ phi x)...
      - firstorder.
      - intros. destruct IHX1. eapply (IHX2 (TIE _ _ _ p x))...
      - intros. apply (IHX (TAllE _ t _ p))...
    Qed.
  End CutElimination.

  Section Soundness.
    Context {b : falsity_flag}.

    Lemma ksoundness_seq A (phi : form) :
      @sprv _ _ _ A None phi  -> kvalid_ctx A phi.
    Proof.
      intros Hprv % seq_ND. now apply ksoundness.
    Qed.
  End Soundness.

  (* **** Enumerability of Sequents *)
  Section Enumerability.
  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.

  Instance eqdec_binop : eq_dec binop.
  Proof.
    intros x y. unfold dec. decide equality.
  Qed.

  Instance eqdec_quantop : eq_dec quantop.
  Proof.
    intros x y. unfold dec. decide equality.
  Qed.

  Definition list_binop (n : nat) := [Impl].

  Instance enum_binop :
    list_enumerator__T list_binop binop.
  Proof.
    intros []; exists 0; cbn; tauto.
  Qed.

  Definition list_quantop (n : nat) := [All].

  Instance enum_quantop :
    list_enumerator__T list_quantop quantop.
  Proof.
    intros []; exists 0; cbn; tauto.
  Qed.

  Lemma enumT_binop :
    enumerable__T binop.
  Proof.
    apply enum_enumT. exists list_binop. apply enum_binop.
  Qed.

  Lemma enumT_quantop :
    enumerable__T quantop.
  Proof.
    apply enum_enumT. exists list_quantop. apply enum_quantop.
  Qed.

  Instance enum_term' :
    list_enumerator__T (L_term _) term :=
    enum_term _.

  Instance enum_form' {ff : falsity_flag} :
    list_enumerator__T (L_form _ _ _ _) form :=
    enum_form _ _ _ _.
  Fixpoint L_seq {b : falsity_flag} (A : list form) (psi : option form) (n : nat) : list form :=
    match n with
    | 0 => match psi with Some psi => [psi] | None => A end
    | S n => L_seq A psi n ++
                  match psi with
     (* Contr *)  | None => concat ([ L_seq A (Some psi) n | psi ∈ A]) ++
     (* IR *)               concat ([ [ phi → psi | psi ∈ L_seq (phi :: A) None n ] | phi ∈ L_T form n]) ++
     (* AllR *)             [ ∀ phi | phi ∈ L_seq ([ psi[↑] | psi ∈ A]) None n ] ++
     (* Absurd *)           ((if b as ff return list (@form _ _ _ ff) -> list (@form _ _ _ ff)
                              then fun _ => [] else fun A => [ phi | phi ∈ L_T form n, ⊥ el L_seq A None n ]) A)
                  | Some psi' => match psi' in @form _ _ _ ff return list (@form _ _ _ ff) -> list (@form _ _ _ ff) with
     (* IL *)         | @bin _ _ _ ff Impl phi psi => fun A => [ xi | xi ∈ L_seq A (Some psi) n, phi el @L_seq ff A None n ]
     (* AllL *)       | quant All psi => fun A => concat ([ [phi | phi ∈ L_seq A (Some psi[t..]) n ] | t ∈ L_T term n])
                      | _ => fun _ => [] end A
                  end
    end.

    Opaque in_dec.

    Lemma enum_sprv {b : falsity_flag} A psi : list_enumerator (L_seq A psi) (sprv A psi).
    Proof with try (eapply cum_ge'; eauto; lia).
      repeat split.
      - rename x into phi. induction 1; try congruence; subst.
        + destruct IHsprv as [m]. exists (S m). cbn. in_app 2.
          eapply in_concat_iff. eexists. split. 2: in_collect phi... all: eauto.
        + destruct IHsprv as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 3.
          eapply in_concat_iff. eexists. split. 2: in_collect phi... in_collect psi...
        + destruct IHsprv as [m]. exists (S m). cbn. in_app 4. in_collect phi...
        + destruct IHsprv as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 5. in_collect phi...
        + exists 0. now left.
        + destruct IHsprv1 as [m1], IHsprv2 as [m2]. exists (1 + m1 + m2). cbn. in_app 2. in_collect xi...
        + destruct IHsprv as [m1], (el_T t) as [m2]. exists (1 + m1 + m2). cbn. in_app 2. eapply in_concat_iff.
          eexists. split. 2: in_collect t... in_collect psi...
      - intros [m]. induction m in A, psi, x, H |-*; destruct psi; cbn in *.
        + destruct H as [-> | []]. apply Ax.
        + eauto.
        + destruct f as [|b P v|b [] phi psi|b [] phi]; inv_collect; eauto.
        + destruct b; inv_collect; eauto.
    Qed.

    Fixpoint L_tseq {b : falsity_flag} (L : nat -> list form) (n : nat) : list form :=
      match n with
      | 0 => nil
      | S n => L_tseq L n ++ concat ([ L_seq A None n | A ∈ L_con L n ])
      end.

    Lemma enum_stprv {b : falsity_flag} T L : list_enumerator L T -> cumulative L -> list_enumerator (L_tseq L) (stprv T).
    Proof with try (eapply cum_ge'; eauto; lia).
      intros He Hcml psi. repeat split.
      - intros (A & [m1] % (enum_el (enum_containsL Hcml He)) & [m2] % (enum_el (enum_sprv A None))).
        exists (1 + (m1 + m2)). cbn. in_app 2. eapply in_concat_iff. eexists. split. 2: in_collect A... idtac...
      - intros [m]. induction m in psi, H |-*; cbn in *. 1: contradiction. inv_collect. exists x0. split.
        + eapply (enum_p (enum_containsL Hcml He)); eassumption.
        + eapply (enum_p (enum_sprv x0 None)); eassumption.
    Qed.
  End Enumerability.
End Gentzen.
