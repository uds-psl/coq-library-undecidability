(** * Tarski Semantics *)

(** ** Generalized Theory Extension **)

From Undecidability.FOLC Require Export ND.

Section GenCons.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Context {b : bottom}.
  Variable GBot : form.
  Hypothesis GBot_closed : closed GBot.

  Notation "⊥" := GBot.
  Notation "A ⊢G phi" := (@prv Sigma class b A phi) (at level 30).
  Notation "T ⊩G phi" := (@tprv Sigma class b T phi) (at level 30).

  Definition econsistent T T' := T' ⊩G ⊥ -> T ⊩G ⊥.

  (* **** Union *)

  Section Union.
    Variable f : nat -> theory.
    Hypothesis econsistent_f : forall n, econsistent (f n) (f (S n)).
    Hypothesis f_le : forall m n, m <= n -> f m ⊑ f n.

    Definition union (f : nat -> theory) := fun t => exists n, f n t.

    Lemma union_f phi :
      union f ⊩G phi -> exists n, f n ⊩G phi.
    Proof.
      intros (A & HA1 & HA2). enough (exists n, A ⊏ f n) as [n H] by now exists n, A.
      clear HA2; induction A.
      - exists 0; firstorder.
      - destruct IHA as [n Hn]; destruct (HA1 a) as [m Hm]; firstorder.
        exists (max n m); intros ? []; subst.
        + eapply f_le; [apply Nat.le_max_r | firstorder]. 
        + eapply f_le; [apply Nat.le_max_l | firstorder].
    Qed.

    Lemma union_sub n :
      f n ⊑ union f.
    Proof.
      firstorder.
    Qed.

    Lemma union_econsistent :
      econsistent (f 0) (union f).
    Proof.
      intros [n H] % union_f. induction n; unfold econsistent in *; eauto.
    Qed.

    Lemma union_closed :
      (forall n, closed_T (f n)) -> closed_T (union f).
    Proof.
      intros f_closed ? n [m H]. now apply f_closed with (n := m) (phi := phi).
    Qed.
  End Union.

  (* **** Explosion *)

  Section Explosion.
    Variable T : theory.
    Hypothesis Hclosed : closed_T T.

    Variable e : nat -> form.
    Hypothesis He : forall phi, exists n, e n = phi.

    Definition exp_axiom phi := ⊥ --> close phi.

    Lemma exp_axiom_lift phi A :
      exp_axiom phi el A -> exp_axiom phi el (map (subst_form form_shift) A).
    Proof.
      intros H. apply in_map_iff. exists (exp_axiom phi). split. 2: assumption.
      apply subst_unused_closed' with (xi := form_shift) (phi0 := exp_axiom phi).
      intros ?. constructor. apply GBot_closed. apply close_closed.
    Qed.

    Fixpoint exp n :=
      match n with
      | 0 => T
      | S n => exp n ⋄ exp_axiom (e n)
      end.
    Definition Exp := union exp.

    Lemma Exp_sub :
      T ⊑ Exp.
    Proof.
      apply union_sub with (n := 0) (f := exp).
    Qed.

    Lemma Exp_econsistent :
      econsistent T Exp.
    Proof.
      apply union_econsistent.
      - intros n (B & HB & Hprv) % prv_T_impl. use_theory B.
        opeirce (close (e n)). oimport Hprv. oapply 0. ctx.
      - induction 1; intros ?; firstorder.
    Qed.

    Lemma Exp_closed :
      closed_T Exp.
    Proof.
      apply union_closed. induction n; intuition. intros ? ? []; intuition; subst.
      constructor; [apply GBot_closed | apply close_closed].
    Qed.

    Definition exploding T := forall phi, (⊥ --> close phi) ∈ T.

    Lemma Exp_exploding :
      exploding Exp.
    Proof.
      intros phi. destruct (He phi) as [n Hn]. exists (S n). right; now subst.
    Qed.

    Lemma exploding_inherit T1 T2 :
      exploding T1 -> T1 ⊑ T2 -> exploding T2.
    Proof.
      firstorder.
    Qed.

  End Explosion. 

  (* **** Proving with explosion axioms *)

  Notation "¬ phi" := (phi --> GBot) (at level 20).
  Notation "∃ phi" := (¬ ∀ ¬ phi) (at level 56, right associativity).

  Ltac ointro_all :=
    match goal with
    | [ |- ?A ⊢ ∀ ?phi] => apply AllI; cbn; asimpl
    end.

  Ltac ointro_impl :=
    match goal with
    | [ |- _  ⊢ (_ --> _)] => apply II
    | [ |- _  ⊢ (¬ _)] => apply II
    end.

  Ltac ointro := ointro_impl + ointro_all + fail "Nothing to intro!".
  Ltac ointros := repeat ointro.

  Lemma GExp A phi :
    (exp_axiom phi) el A -> A ⊢G ⊥ -> A ⊢G phi.
  Proof.
    intros Hel Hbot. apply close_extract. exact (IE (Ctx Hel) Hbot).
  Qed.

  Ltac oexfalso := apply GExp; [intuition |].

  Lemma GDN A phi :
    (exp_axiom phi) el A -> A ⊢G ¬ (¬ phi) -> A ⊢G phi.
  Proof.
    intros Hx H.
    oimport (Pc A phi GBot). oimport H. oapply 1. ointros. oexfalso. oapply 1. ctx.
  Qed.

  Ltac oindirect := apply GDN; [intuition| apply II].
  Ltac clean H := unfold subst1; rewrite! (subst_unused_closed' _ H).
  Ltac clean_GBot := clean GBot_closed.

  Lemma GExE A phi psi :
    exp_axiom psi el A -> A ⊢G (∃ phi) -> (phi :: map (subst_form form_shift) A) ⊢G psi[↑] -> A ⊢G psi.
  Proof.
    intros Hx Hex Hinst.
    oindirect. oimport Hex. oapply 0. ointros. clean_GBot. oapply 2. ouse Hinst. 
  Qed.

  Ltac odestruct n := eapply GExE; [intuition|ctx_index n|]; cbn; asimpl.

  Lemma GExI A t phi :
    A ⊢G phi [t .: ids] -> A ⊢G ∃ phi.
  Proof.
    intros Hc. apply II.
    ospecialize 0 t. clean_GBot. oapply 0. ouse Hc.
  Qed.

  Ltac oexists t :=
    eapply (@GExI _ t); cbn; asimpl.

  Lemma GXM A phi psi :
    exp_axiom psi el A -> (phi :: A) ⊢G psi -> (¬ phi :: A) ⊢G psi -> A ⊢G psi.
  Proof.
    intros Hx Ht Hf. oindirect.
    oassert (¬ phi). ointros. oapply 1. ouse Ht. oapply 1. ouse Hf.
  Qed.

  Ltac oxm form :=
    apply (@GXM _ form); [intuition| |].

  Definition DPexp1 phi := exp_axiom (∃ (phi --> (∀ phi)[↑])).
  Definition DPexp2 phi := exp_axiom (phi [(var_term O) .: (shift >> (shift >> var_term))]).
  Definition DPexp3 phi := exp_axiom phi.

  Lemma GDP A phi :
    DPexp1 phi el A -> DPexp2 phi el A -> DPexp3 phi el A -> A ⊢G ∃ (phi --> (∀ phi)[↑]).
  Proof.
    intros ? H1 H2. do 2 apply exp_axiom_lift in H1. do 1 apply exp_axiom_lift in H2. oxm (∃ (¬ phi)).
    - odestruct 0. clean_GBot. oexists (var_term 0). ointros. oexfalso. clean_GBot. oapply 1. ctx.
    - oexists (var_term 0). ointros. oindirect. clean_GBot. oapply 2. oexists (var_term 0). clean_GBot. ctx.
  Qed.

  (* **** Henkin *)

  Section Henkin.
    Variable T : theory.
    Hypothesis Hclosed : closed_T T.
    Hypothesis Hexp : exploding T.

    Variable e : nat -> form.
    Hypothesis He : forall phi, exists n, e n = phi.
    Hypothesis Hunused : forall n m, n <= m -> unused m (e n).

    Definition henkin_axiom phi := (phi --> ((∀ phi)[↑])). 

    Lemma henkin_axiom_unused n phi :
      unused n (∀ phi) -> unused (S n) (¬ (henkin_axiom phi)).
    Proof.
      inversion 1. unfold henkin_axiom. constructor; [| apply GBot_closed].
      capply uf_Impl. capply unused_after_subst. subst. intros x.
      decide (x = n). 1: subst; now left. right; constructor; congruence.
    Qed.

    Fixpoint henkin n :=
      match n with
      | O => T
      | S n => henkin n ⋄ subst_form ((var_term n)..) (henkin_axiom (e n))
      end.

    Lemma henkin_unused n :
      forall phi m, phi ∈ (henkin n) -> n <= m -> unused m phi.
    Proof.
      induction n; cbn.
      - intros. now apply Hclosed.
      - intros phi [| m] H1 H2. omega.
        assert (unused (S m) (e n)) by (apply Hunused; omega).
        assert (unused (S (S m)) (e n)) by (apply Hunused; omega).
        assert (unused m (e n)) by (apply Hunused; omega).
        destruct H1. capply IHn. omega. subst. constructor.
        + apply unused_after_subst. intros []; comp. 1: right; constructor; omega.
          decide (S m = n0). 1: subst; now left. right; constructor; omega.
        + constructor. asimpl. assumption.
    Qed.

    Lemma henkin_le m n :
      m <= n -> henkin m ⊑ henkin n.
    Proof.
      induction 1; firstorder.
    Qed.

    Definition Henkin := union henkin.

    Lemma Henkin_consistent :
      econsistent T Henkin.
    Proof.
      refine (union_econsistent _ henkin_le). intros n.
      assert (unused n (e n)) by now apply Hunused.
      cbn; intros (A & HA1 & HA2) % prv_T_impl.
      rewrite <- (subst_unused_closed' ((var_term n)..) GBot_closed) in HA2.
      apply -> (@nameless_equiv Sigma class b _ _ A (¬ (henkin_axiom (e n))) n) in HA2.
      - use_theory (exp_axiom GBot :: DPexp1 (e n) :: DPexp2 (e n) :: DPexp3 (e n) :: A). shelve.
        oimport (@GDP (exp_axiom GBot :: DPexp1 (e n) :: DPexp2 (e n) :: DPexp3 (e n) :: A) (e n)).
        odestruct 0. oimport HA2. shelve. clean_GBot. oapply 0. ctx.
      - apply henkin_axiom_unused; constructor; apply Hunused; omega.
      - intros ? H' % HA1. eapply henkin_unused. apply H'. constructor.
      Unshelve.
        + intros ? [<- | [<- | [ <- | [<- |]]]]. 5: intuition.
          all: apply henkin_le with (m := 0); [omega | apply Hexp]. 
        + intros ? ?. now do 6 right.
    Qed.

    Definition is_Henkin T := forall T' phi, T ⊑ T' -> (forall t, T' ⊩G phi[t..]) -> T' ⊩G ∀ phi.

    Lemma Henkin_is_Henkin :
      is_Henkin Henkin.
    Proof.
      intros T' phi HT' Hall. destruct (He phi) as [n Hn]. destruct (Hall (var_term n)) as (A & HA1 & HA2).
      use_theory (subst_form ((var_term n)..) (henkin_axiom phi) :: A).
      - intros ? [<- |]; [| intuition]; subst. apply HT'. exists (S n). now right.
      - oimport HA2. comp. oapply 1. ctx.
    Qed.

    Lemma is_Henkin_inherit T1 T2 :
      is_Henkin T1 -> T1 ⊑ T2 -> is_Henkin T2.
    Proof.
      firstorder.
    Qed.

    Lemma Henkin_T :
      T ⊑ Henkin.
    Proof.
      apply union_sub with (f := henkin) (n := 0).
    Qed.
  End Henkin.

  (* **** Omega *)

  Section Omega.
    Variable e : nat -> form.
    Hypothesis He : forall phi, exists n, e n = phi.

    Variable T : theory.
    Hypothesis Hexp : exploding T.
    Hypothesis Hhenkin : is_Henkin T.

    Definition maximal T := forall f, econsistent T (T ⋄ f) -> f ∈ T.

    Definition econsistent_join T phi := fun psi => T psi \/ (econsistent T (T ⋄ phi) /\ psi = phi).
    Infix "∘" := econsistent_join (at level 20).

    Lemma econsistent_join_sub T' phi :
      (T' ∘ phi) ⊑ (T' ⋄ phi).
    Proof.
      firstorder.
    Qed.

    Lemma consistent_join_step T' phi psi :
      T' ∘ psi ⊩G phi -> T' ⊩G phi \/ econsistent T' (T' ⋄ psi).
    Proof.
      intros (A & HA1 & HA2).
      enough (A ⊏ T' \/ econsistent T' (T' ⋄ psi)) as [] by ((left; exists A; intuition) + now right).
      clear HA2; induction A.
      - firstorder.
      - destruct (HA1 a), IHA; intuition. all: eauto with contains_theory.
    Qed.

    Fixpoint omega n : theory :=
      match n with
      | 0 => T
      | S n => omega n ∘ e n
      end.

    Lemma omega_le n m :
      n <= m -> omega n ⊑ omega m.
    Proof.
      induction 1; firstorder.
    Qed.

    Definition Omega : theory := union omega.

    Lemma econsistent_Omega :
      econsistent T Omega.
    Proof.
      refine (union_econsistent _ omega_le). intros n H. destruct (consistent_join_step H).
      all: firstorder.
    Qed.

    Lemma econsistency_inheritance T1 T2 T1' T2' :
      econsistent T1 T1' -> T1 ⊑ T2 -> T2' ⊑ T1' -> econsistent T2 T2'.
    Proof.
      firstorder.
    Qed.

    Lemma econsistency_trans T1 T2 T3 :
      econsistent T1 T2 -> econsistent T2 T3 -> econsistent T1 T3.
    Proof.
      firstorder.
    Qed.

    Lemma maximal_Omega :
      maximal Omega.
    Proof.
      intros phi H. destruct (He phi) as [n Hn].
      apply (union_sub (n := S n)); cbn; rewrite -> Hn. right; split; [| reflexivity].
      eapply econsistency_inheritance.
      + exact (econsistency_trans econsistent_Omega H).
      + apply omega_le with (n := 0). omega.
      + firstorder.
    Qed.

    Lemma econsistent_prv T' T'' phi :
      econsistent T' T'' -> T'' ⊩G phi -> econsistent T' (T'' ⋄ phi).
    Proof.
      intros HT Hphi Hbot. now apply HT, (prv_T_remove Hphi).
    Qed.

    Lemma maximal_prv T' phi :
      maximal T' -> T' ⊩G phi -> phi ∈ T'.
    Proof.
      intros Hin Hprv. now apply Hin, econsistent_prv.
    Qed.

    Lemma Omega_prv phi :
      Omega ⊩G phi -> phi ∈ Omega.
    Proof.
      intros Hprv. now apply (maximal_prv maximal_Omega).
    Qed.

    Lemma Omega_T :
      T ⊑ Omega.
    Proof.
      change T with (omega 0). apply (union_sub (n := 0)).
    Qed.

    Lemma Omega_impl phi psi :
      phi --> psi ∈ Omega <-> (phi ∈ Omega -> psi ∈ Omega).
    Proof.
      split.
      - intros Himp Hphi. apply Omega_prv.
        use_theory [phi --> psi; phi]. oapply 0. ctx.
      - intros H. apply maximal_Omega. intros (A & HA1 & HA2) % prv_T_impl.
        apply (prv_T_remove (phi := psi)).
        + apply elem_prv, H, Omega_prv.
          use_theory (exp_axiom phi :: exp_axiom psi :: A).
          * intros ? [<- | [ <- | H'']]; [apply Omega_T, Hexp | apply Omega_T, Hexp | now apply HA1].
          * oindirect. oimport HA2. oapply 0. ointros. oexfalso. oapply 2. ctx.
        + use_theory (psi :: A). oimport HA2. oapply 0. ointros. ctx.
    Qed.

    Lemma Omega_all phi :
      ∀ phi ∈ Omega <-> (forall t, phi[t..] ∈ Omega).
    Proof.
      split; intros Hprv.
      - intros t. apply Omega_prv. use_theory [∀ phi]. ospecialize 0 t. ctx.
      - apply Omega_prv, (Hhenkin Omega_T). eauto using elem_prv.
    Qed.
  End Omega.
End GenCons.

(* **** Conclusion *)

Section Composition.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Structure ConstructionInputs : Type :=
    {
      NBot : form ;
      NBot_closed : closed NBot ;
      
      variant : bottom ;

      In_T : theory ;
      In_T_closed : closed_T In_T ;

      enum : nat -> form ;
      enum_enum : forall phi, exists n, enum n = phi ;
      enum_unused : forall n m, n <= m -> unused m (enum n)
    }.

  Structure ConstructionOutputs (In : ConstructionInputs) :=
    {
      Out_T : theory ;
      Out_T_econsistent : @econsistent Sigma (variant In) (NBot In) (In_T In) Out_T ;
      Out_T_sub : In_T In ⊑ Out_T ;

      Out_T_prv : forall phi, @tprv Sigma class (variant In) Out_T phi -> phi ∈ Out_T ;
      Out_T_all : forall phi, ∀ phi ∈ Out_T <-> (forall t, phi[t..] ∈ Out_T) ;
      Out_T_impl : forall phi psi, phi --> psi ∈ Out_T <-> (phi ∈ Out_T -> psi ∈ Out_T)
    }.

  Lemma construct_construction (In : ConstructionInputs) :
    ConstructionOutputs In.
  Proof.
    destruct In as [NBot NBot_closed system T T_closed e e_enum e_unused].
    eexists (Omega NBot e (Henkin (Exp NBot T e) e)); cbn.
    + capply econsistency_trans. capply econsistency_trans. capply Exp_econsistent.
      capply Henkin_consistent. capply Exp_closed. capply Exp_exploding. capply econsistent_Omega.
    + transitivity (Henkin (Exp NBot T e) e). transitivity (Exp NBot T e).
      apply Exp_sub. apply Henkin_T. apply Omega_T.
    + capply Omega_prv.
    + capply Omega_all. capply Henkin_is_Henkin.
    + capply Omega_impl. capply exploding_inherit.
      - capply Exp_exploding.
      - capply Henkin_T.
  Qed.
End Composition.
