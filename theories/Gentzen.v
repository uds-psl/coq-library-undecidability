(** ** Normal Sequent Calculus **)

From Equations Require Import Equations.
From Undecidability.FOLC Require Export ND.
From Undecidability.FOLC Require Export Kripke.

Section Gentzen.
  Context {Sigma : Signature}.

  Inductive sprv : forall (b : bottom), list form -> option form -> form -> Prop :=
  | Contr {b} A phi psi : sprv b A (Some phi) psi -> phi el A -> sprv b A None psi
  | IR {b} A phi psi : sprv b (phi :: A) None psi -> sprv b A None (phi --> psi)
  | AllR {b} A phi : sprv b (map (subst_form form_shift) A) None phi -> sprv b A None (∀ phi)
  | Absurd A phi : sprv expl A None ⊥ -> sprv expl A None phi
  | Ax {b} A phi : sprv b A (Some phi) phi
  | IL {b} A phi psi xi : sprv b A None phi -> sprv b A (Some psi) xi -> sprv b A (Some (phi --> psi)) xi
  | AllL {b} A phi t psi : sprv b A (Some (phi [t .: ids])) psi -> sprv b A (Some (∀ phi)) psi.

  Notation "A '⊢S' phi" := (sprv _ A None phi) (at level 30).
  Notation "A ';;' phi '⊢s' psi" := (sprv _ A (Some phi) psi) (at level 70).
  Arguments sprv {_} _ _ _.

  Definition stprv {b : bottom} (T : theory) (phi : form) : Prop :=
    exists A, A ⊏ T /\ sprv A None phi.

  Hint Constructors sprv.

  Lemma seq_consistent {b : bottom} :
    ~ [] ⊢S ⊥.
  Proof.
    remember nil. remember Fal. remember None. remember b.
    induction 1; subst; intuition congruence.
  Qed.

  Section Weakening.
    Context {b : bottom}.

    Lemma seq_Weak A B phi psi :
      sprv A phi psi -> A <<= B -> sprv B phi psi.
    Proof.
      intros H; induction H in B |-*; intuition; eauto using incl_map. 
    Qed.

    Theorem seq_subst_Weak  A phi psi sigma :
      sprv A phi psi -> sprv ([phi[sigma] | phi ∈ A]) (option_map (subst_form sigma) phi) psi[sigma].
    Proof.
      induction 1 in sigma |-*; comp; eauto using in_map.
      - apply AllR. setoid_rewrite map_map in IHsprv. erewrite map_map, map_ext.
        apply IHsprv. intros ?. comp. now apply ext_form.
      - specialize (IHsprv sigma). apply AllL with (t0 := t [sigma]). comp. now asimpl in IHsprv.
    Qed.

    Lemma seq_nameless_equiv A phi n :
      unused_L n A -> unused (S n) phi -> ((A ⊢S phi[(var_term n)..]) <-> [phi[↑] | phi ∈ A] ⊢S phi).
    Proof.
      intros HL Hphi. split.
      - intros H % (seq_subst_Weak (cycle_shift n)). rewrite cycle_shift_subject,
          (map_ext_in _ (subst_form form_shift)) in H. 1,3: assumption. intros ? ? % HL.
        now apply (@cycle_shift_shift Sigma).
      - intros H % (seq_subst_Weak ((var_term n)..)). rewrite map_map in *. rewrite (map_ext _ id), map_id in H.
        assumption. intuition comp. erewrite ext_form. now asimpl. intros []; now asimpl.
    Qed.
  End Weakening.

  (* **** Normalization *)
  
  (* We redefine sprv and prv in Type so we define predicates on them. *)
  Inductive tsprv : forall (b : bottom), list form -> option form -> form -> Type :=
  | TContr {b} A phi psi : tsprv b A (Some phi) psi -> phi el A -> tsprv b A None psi
  | TIR {b} A phi psi : tsprv b (phi :: A) None psi -> tsprv b A None (phi --> psi)
  | TAllR {b} A phi : tsprv b (map (subst_form form_shift) A) None phi -> tsprv b A None (∀ phi)
  | TAbsurd A phi : tsprv expl A None Fal -> tsprv expl A None phi
  | TAx {b} A phi : tsprv b A (Some phi) phi
  | TIL {b} A phi psi xi : tsprv b A None phi -> tsprv b A (Some psi) xi -> tsprv b A (Some (phi --> psi)) xi
  | TAllL {b} A phi t psi : tsprv b A (Some (phi [t .: ids])) psi -> tsprv b A (Some (∀ phi)) psi.
  Arguments tsprv {_} _ _ _.

  Inductive tprv : forall (b : bottom), list (form) -> form -> Type :=
  | TII A {b} phi psi : tprv b (phi::A) psi -> tprv b A (phi --> psi)
  | TIE A {b} phi psi : tprv b A (phi --> psi) -> tprv b A phi -> tprv b A psi
  | TAllI A {b} phi : tprv b (map (subst_form form_shift) A) phi -> tprv b A (∀ phi)
  | TAllE A {b} t phi : tprv b A (All phi) -> tprv b A (phi [t .: ids])
  | TExp A phi : tprv expl A Fal -> tprv expl A phi
  | TCtx A {b} phi : phi el A -> tprv b A phi.
  Arguments tprv {_} _ _.

  Definition not_II {b : bottom} A phi (p : tprv A phi) : Prop :=
    match p with
    | (TII p') => False
    | (TAllI p') => True
    | (TAllE _ p') => True
    | (TExp _ p') => True
    | (TIE p' p'') => True
    | (TCtx _) => True
    end.

  Definition not_AllI {b : bottom} A phi (p : tprv A phi) : Prop :=
    match p with
    | (TII p') => True
    | (TAllI p') => False
    | (TAllE _ p') => True
    | (TExp _ p') => True
    | (TIE p' p'') => True
    | (TCtx _) => True
    end.

  Fixpoint normal {b : bottom} A phi (p : tprv A phi) : Prop :=
    match p with
    | (TII p') => normal p'
    | (TIE p' p'') => normal p' /\ normal p'' /\ not_II p'
    | (TAllI p') => normal p'
    | (TAllE _ p') => normal p' /\ not_AllI p'
    | (TExp _ p') => normal p'
    | (TCtx _) => True
    end.

  Section CutElimination.
    Context {b : bottom}.

    Definition embed A phi psi :=
      match phi with
      | Some phi' => @prv _ intu b A phi' -> @prv _ intu b A psi
      | None => @prv _ intu b A psi
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
      stprv T phi -> @ND.tprv _ intu b T phi.
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
      - apply (IHX (TCtx i))...
      - destruct IHX. exists (TII x)...
      - destruct IHX. exists (TAllI x)...
      - destruct IHX. exists (TExp phi x)...
      - firstorder.
      - intros. destruct IHX1. eapply (IHX2 (TIE p x))...
      - intros. apply (IHX (TAllE t p))...
    Qed.
  End CutElimination.

  Section Soundness.
    Context {b : bottom}.

    Lemma ksoundness_seq A C (phi : form) :
      (b = expl -> kcon_subs kexploding C) -> @sprv _ A None phi  -> kvalid_L C A phi.
    Proof.
      intros Hexp Hprv % seq_ND. now apply ksoundness.
    Qed.
  End Soundness.

  (* **** Enumerability of Sequents *)
  Section Enumerability.
    Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
    Context {HeF : enumT Funcs} {HeP : enumT Preds}.
    
    Fixpoint L_seq {b : bottom} (A : list form) (psi : option form) (n : nat) : list form :=
      match n with
      | 0 => match psi with Some psi => [psi] | None => A end
      | S n => L_seq A psi n ++
                    match psi with
       (* Contr *)  | None => concat ([ L_seq A (Some psi) n | psi ∈ A]) ++
       (* IR *)               concat ([ [ phi --> psi | psi ∈ L_seq (phi :: A) None n ] | phi ∈ L_T form n]) ++
       (* AllR *)             [ ∀ phi | phi ∈ L_seq ([ psi[↑] | psi ∈ A]) None n ] ++
       (* Absurd *)           (if b then [ phi | phi ∈ L_T form n, ⊥ el L_seq A None n ] else [])
       (* IL *)     | Some (phi --> psi) => [ xi | xi ∈ L_seq A (Some psi) n, phi el L_seq A None n ]
       (* AllL *)   | Some (∀ psi) => concat ([ [phi | phi ∈ L_seq A (Some psi[t..]) n ] | t ∈ L_T term n])
                    | _ => []
                    end
      end.

    Opaque in_dec.

    Lemma enum_sprv {b : bottom} A psi : enum (sprv A psi) (L_seq A psi).
    Proof with try (eapply cum_ge'; eauto; omega).
      repeat split.
      - eauto.
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
        + destruct f; inv_collect; eauto.
        + destruct b; inv_collect; eauto.
    Qed.

    Fixpoint L_tseq {b : bottom} (L : nat -> list form) (n : nat) : list form :=
      match n with
      | 0 => nil
      | S n => L_tseq L n ++ concat ([ L_seq A None n | A ∈ L_con L n ])
      end.

    Lemma enum_stprv {b : bottom} T L : enum T L -> enum (stprv T) (L_tseq L).
    Proof with try (eapply cum_ge'; eauto; omega).
      intros He. repeat split.
      - eauto.
      - intros (A & [m1] % (enum_el (enum_containsL He)) & [m2] % (enum_el (enum_sprv A None))).
        exists (1 + m1 + m2). cbn. in_app 2. eapply in_concat_iff. eexists. split. 2: in_collect A... idtac...
      - intros [m]. induction m in x, H |-*; cbn in *. 1: contradiction. inv_collect. exists x1. split.
        + eapply (enum_p (enum_containsL He)); eassumption.
        + eapply (enum_p (enum_sprv x1 None)); eassumption.
    Qed.
  End Enumerability.
End Gentzen.

Notation "A '⊢S' phi" := (sprv _ A None phi) (at level 30).
Notation "A ';;' phi '⊢s' psi" := (sprv _ A (Some phi) psi) (at level 70).
Notation "A '⊢SE' phi" := (sprv expl A None phi) (at level 30).
Notation "A ';;' phi '⊢sE' psi" := (sprv expl A (Some phi) psi) (at level 70).
Notation "A '⊢SL' phi" := (sprv lconst A None phi) (at level 30).
Notation "A ';;' phi '⊢sL' psi" := (sprv lconst A (Some phi) psi) (at level 70).
Arguments sprv {_} _ _ _.
Notation "T '⊩SE' phi" := (@stprv _ expl T phi) (at level 30).
