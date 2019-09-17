(* * Natural Deduction *)

From Undecidability.FOLC Require Export FullFOL.

Inductive peirce := class | intu.
Inductive bottom := expl | lconst.
Existing Class peirce.
Existing Class bottom.

Section ND_def.
  Context {Sigma : Signature}.

  Definition form_shift : nat -> term :=
    fun n => var_term (S n).

  Notation "↑" := (form_shift).

  Reserved Notation "A ⊢ phi" (at level 61).
  
  (* ** Definition *)

  Implicit Type p : peirce.
  Implicit Type b : bottom.

  Inductive prv : forall (p : peirce) (b : bottom), list (form) -> form -> Prop :=
  | II {p b} A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi
  | IE {p b} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | AllI {p b} A phi : [psi[↑] | psi ∈ A] ⊢ phi -> A ⊢ ∀ phi
  | AllE {p b} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
  | ExI {p b} A t phi : A ⊢ phi[t..] -> A ⊢ ∃ phi
  | ExE {p b} A phi psi : A ⊢ ∃ phi -> phi::[theta[↑] | theta ∈ A] ⊢ psi[↑] -> A ⊢ psi
  | Exp {p} A phi : prv p expl A ⊥ -> prv p expl A phi
  | Ctx {p b} A phi : phi el A -> A ⊢ phi
  | CI {p b} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 {p b} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 {p b} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
  | DI1 {p b} A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
  | DI2 {p b} A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
  | DE {p b} A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
  | Pc {b} A phi psi : prv class b A (((phi --> psi) --> phi) --> phi)
  where "A ⊢ phi" := (prv _ _ A phi).

  Arguments prv {_ _} _ _.

  Hint Constructors prv.

  Notation "A ⊢ phi" := (prv A phi) (at level 61).
  Notation "A '⊢(' p , b ')' phi" := (@prv p b A phi) (at level 30).
  Notation "A ⊢CE phi" := (@prv class expl A phi) (at level 30).
  Notation "A ⊢CL phi" := (@prv class lconst A phi) (at level 30).
  Notation "A ⊢IE phi" := (@prv intu expl A phi) (at level 30).

  Definition tprv p b T phi := (exists A, A ⊏ T /\ @prv p b A phi).
  Arguments tprv {_ _} _ _.

  Notation "T ⊩ phi" := (tprv T phi) (at level 30).
  Notation "T '⊩(' s , b ')' phi" := (@tprv s b T phi)  (at level 30).
  Notation "T ⊩CE phi" := (@tprv class expl T phi) (at level 30).
  Notation "T ⊩CL phi" := (@tprv class lconst T phi) (at level 30).
  Notation "T ⊩IE phi" := (@tprv intu expl T phi) (at level 30).

  Section Weakening.
    Context {p : peirce} {b : bottom}.

    Theorem Weak A B phi :
      A ⊢ phi -> A <<= B -> B ⊢ phi.
    Proof.
      intros H. revert B. induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
      - eapply AllI; eauto using incl_map.
      - eapply ExE; eauto using incl_map.
    Qed.

    Lemma up_term_term (t : term) xi :
      t[↑][up_term xi] = t[xi][↑].
    Proof.
      now asimpl.
    Qed.

    Lemma up_term_form xi psi :
      psi[↑][up_term xi] = psi[xi][↑].
    Proof.
      now asimpl.
    Qed.
    
    Theorem subst_Weak A phi xi :
      A ⊢ phi -> [phi[xi] | phi ∈ A] ⊢ phi[xi].
    Proof.
      induction 1 in xi |-*; comp.
      1-2,7-15: eauto using in_map.
      - apply AllI. setoid_rewrite map_map in IHprv. erewrite map_map, map_ext.
        apply IHprv. intros ?. comp. now apply ext_form.
      - specialize (IHprv xi). apply AllE with (t0 := t [xi]) in IHprv. comp. now asimpl in IHprv.
      - specialize (IHprv xi). eapply ExI with (t0 := t [xi]). asimpl. now asimpl in IHprv.
      - eapply ExE in IHprv1. eassumption. rewrite map_map.
        specialize (IHprv2 (up_term xi)). erewrite <- up_term_form.
        erewrite map_map, map_ext in IHprv2. apply IHprv2.
        apply up_term_form.
    Qed.

    Lemma Weak_T T1 T2 phi :
      T1 ⊩ phi -> T1 ⊑ T2 -> T2 ⊩ phi.
    Proof.
      intros (A & HA1 & HA2) HT2. exists A; firstorder.
    Qed.

    Definition cycle_shift n x :=
      if Dec (n = x) then var_term 0 else var_term (S x).

    Hint Unfold cycle_shift.

    Lemma cycle_shift_shift n phi :
      unused n phi -> phi[cycle_shift n] = phi[↑].
    Proof.
      intros H. apply (subst_unused_single H). intros m ?. unfold cycle_shift. now decide (n = m).
    Qed.

    Lemma cycle_shift_subject n phi :
      unused (S n) phi -> phi[(var_term n)..][cycle_shift n] = phi.
    Proof.
      intros H. asimpl. rewrite (@subst_unused_single _ _ ids _ _ H). 1: now asimpl.
      intros m H'; comp; decide (n = n); try congruence. destruct m; [reflexivity |].
        comp; decide (n = m); comp; congruence.
    Qed.

    Lemma nameless_equiv A phi n :
      unused_L n A -> unused (S n) phi -> ((A ⊢ phi[(var_term n)..]) <-> [phi[↑] | phi ∈ A] ⊢ phi).
    Proof.
      intros HL Hphi. split.
      - intros H % (subst_Weak (cycle_shift n)). rewrite cycle_shift_subject,
          (map_ext_in _ (subst_form form_shift)) in H. 1,3: assumption. intros ? ? % HL.
        now apply cycle_shift_shift.
      - intros H % (subst_Weak ((var_term n)..)). rewrite map_map in *. rewrite (map_ext _ id), map_id in H.
        assumption. now intuition comp.
    Qed.

    Lemma nameless_equiv_all A phi n :
      unused_L n A -> unused (S n) phi -> ((A ⊢ phi[(var_term n)..]) <-> [phi[↑] | phi ∈ A] ⊢ phi).
    Proof.
      intros HL Hphi. split.
      - intros H % (subst_Weak (cycle_shift n)). rewrite cycle_shift_subject,
          (map_ext_in _ (subst_form form_shift)) in H. 1,3: assumption. intros ? ? % HL.
        now apply cycle_shift_shift.
      - intros H % (subst_Weak ((var_term n)..)). rewrite map_map in *. rewrite (map_ext _ id), map_id in H.
        assumption. now intuition comp.
    Qed.

    Lemma nameless_equiv_ex A phi psi n :
      unused_L n A -> unused n phi -> unused (S n) psi
      -> (psi[(var_term n)..]::A) ⊢ phi <-> (psi::[p[↑] | p ∈ A]) ⊢ phi[↑].
    Proof.
      intros HL Hphi Hpsi. split.
      - intros H % (subst_Weak (cycle_shift n)). cbn in *.
        rewrite (map_ext_in _ (subst_form form_shift)), cycle_shift_subject, cycle_shift_shift in H; trivial.
        intros a Ha. specialize (HL a Ha). now rewrite cycle_shift_shift.
      - intros H % (subst_Weak ((var_term n)..)). cbn in *.
        rewrite map_map, (map_ext _ id), map_id in H.
        + now asimpl in H.
        + intros. now comp.
    Qed.
    
  End Weakening.

  Lemma prv_cut {p : peirce} {b : bottom} A phi psi :
    A ⊢ phi -> (phi :: A) ⊢ psi -> A ⊢ psi.
  Proof.
    eauto.
  Qed.

  Lemma tprv_list_T {p : peirce} {b : bottom} A phi :
    list_T A ⊩ phi -> A ⊢ phi.
  Proof.
    intros (B & HB1 & HB2). apply (Weak HB2). firstorder.
  Qed.

  Definition capture_subs n x := var_term (x + n).

  Lemma capture_extract {p : peirce} {b : bottom} n A phi :
    A ⊢ subst_form (capture_subs n) (capture n phi) -> A ⊢ subst_form (capture_subs 0) phi.
  Proof.
    induction n; comp; intuition. apply IHn. apply (AllE (var_term n)) in H. asimpl in H.
    erewrite ext_form. 1: apply H. intros [| x]; unfold capture_subs; cbn; f_equal; omega.
  Qed.

  Lemma close_extract {p : peirce} {b : bottom} A phi :
    A ⊢ close phi -> A ⊢ phi.
  Proof.
    intros H. assert (Hclosed : closed (close phi)) by apply close_closed.
    unfold close in *. destruct (find_unused phi) as [n Hn]; cbn in *.
    rewrite <- subst_unused_closed' with (xi := capture_subs n) in H. 2: firstorder.
    apply capture_extract in H. rewrite idSubst_form in H; intuition.
    destruct x; unfold capture_subs; f_equal; omega.
  Qed.

  Lemma big_imp_extract {p : peirce} {b : bottom} A B phi :
    B ⊢ (big_imp A phi) -> (rev A ++ B) ⊢ phi.
  Proof.
    induction A in B |-*.
    - tauto.
    - cbn. intros Hprv. rewrite <- app_assoc. comp.
      apply IHA. eapply IE. 1: apply (Weak Hprv); intuition.
      now apply Ctx.
  Qed.

  Lemma prv_from_single {p : peirce} { b : bottom} A phi :
    nil ⊢ close (A ⟹ phi) -> A ⊢ phi.
  Proof.
    intros Hprv % close_extract. apply big_imp_extract in Hprv.
    eapply Weak. apply Hprv. rewrite app_nil_r. now intros ? ? % in_rev.
  Qed.
End ND_def.

Hint Constructors prv.

Arguments prv {_ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 30).
Notation "A '⊢(' p , b ')' phi" := (@prv _ p b A phi) (at level 30).
Notation "A ⊢CE phi" := (@prv _ class expl A phi) (at level 30).
Notation "A ⊢CL phi" := (@prv _ class lconst A phi) (at level 30).
Notation "A ⊢IE phi" := (@prv _ intu expl A phi) (at level 30).

Arguments tprv {_ _ _} _ _.
Notation "T ⊩ phi" := (tprv T phi) (at level 30).
Notation "T '⊩(' s , b ')' phi" := (@tprv _ s b T phi)  (at level 30).
Notation "T ⊩CE phi" := (@tprv _ class expl T phi) (at level 30).
Notation "T ⊩CL phi" := (@tprv _ class lconst T phi) (at level 30).
Notation "T ⊩IE phi" := (@tprv _ intu expl T phi) (at level 30).

(* ** Proof Tacticts *)

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

Ltac ctx_index' n :=
  match n with
  | O => now left
  | S ?m => right; ctx_index' m
  end.
Ltac ctx_index n := apply Ctx; ctx_index' n.
Ltac ctx := apply Ctx; intuition.

Ltac oapply n := eapply IE; [ctx_index n|].

Ltac ospecialize n t :=
  eapply prv_cut; [eapply (@AllE _ _ _ _ t); ctx_index n|]; cbn; asimpl.

Ltac ouse H := eapply Weak; [apply H |]; intuition.
Ltac oimport H := eapply prv_cut; [ouse H |].
Ltac oassert form := eapply (@prv_cut _ _ _ _ form).
Ltac oexfalso := apply Exp.
Ltac opeirce form := eapply IE; [apply (@Pc _ _ _ _ form) | apply II].

Lemma DN {Sigma : Signature} A phi :
  A ⊢CE ¬ (¬ phi) -> A ⊢CE phi.
Proof.
  intros H. oimport H. opeirce Fal. oexfalso. oapply 1. ctx.
Qed.

Ltac oindirect := apply DN, II.

Notation "c∃ phi" := (¬ ∀ ¬ phi) (at level 56, right associativity).

Lemma ExE' {Sigma : Signature} A phi psi :
  A ⊢CE (c∃ phi) -> (phi :: [phi[↑] | phi ∈ A]) ⊢CE psi[↑] -> A ⊢CE psi.
Proof.
  intros Hex Hinst.
  oindirect. oimport Hex. oapply 0.
  ointros. oapply 2. ouse Hinst.
Qed.

Ltac odestruct n := eapply ExE'; [ctx_index n|]; cbn; asimpl.

Lemma ExI' {Sigma : Signature} {p : peirce} {b : bottom} A t phi :
  A ⊢ phi [t..] -> A ⊢ c∃ phi.
Proof.
  intros Hc. apply II. ospecialize 0 t. oapply 0. ouse Hc.
Qed.

Ltac oexists t :=
  eapply (@ExI' _ _ _ _ t); cbn; asimpl.

Ltac osplit := eapply CI.
Ltac oleft := eapply DI1.
Ltac oright := eapply DI2.

Lemma AXM {Sigma : Signature} A phi psi :
  (phi :: A) ⊢CE psi -> (¬ phi :: A) ⊢CE psi -> A ⊢CE psi.
Proof.
  intros Ht Hf. oindirect. oassert (¬ phi). ointros. oapply 1.
  ouse Ht. oapply 1. ouse Hf.
Qed.

Ltac oxm form :=
  apply (@AXM _ _ form).

Lemma DP {Sigma : Signature} phi :
  [] ⊢CE c∃ (phi --> (∀ phi)[↑]).
Proof.
  oxm (c∃ ¬ phi).
  - odestruct 0. oexists (var_term 0). ointros. oexfalso. oapply 1. ctx.
  - oexists (var_term 0). ointros. oindirect. oapply 2. oexists (var_term 0). ctx.
Qed.

(* ** Theory manipulation *)

Section TheoryManipulation.
  Context {Sigma : Signature}.
  Context {p : peirce} {b : bottom}.
  Context {HF : eq_dec Funcs} {HP : eq_dec Preds}.

  Lemma prv_T_impl T phi psi :
    (T ⋄ phi) ⊩ psi -> T ⊩ (phi --> psi).
  Proof.
    intros (A & HA1 & HA2). exists (rem A phi); split.
    - intros f [[] % HA1 Hf2] % in_rem_iff; subst; intuition.
    - eapply II, Weak. 1: apply HA2. transitivity (phi :: A). 1: eauto. apply rem_equi.
  Qed.

  Lemma prv_T_remove T phi psi :
    T ⊩ phi -> T ⋄ phi ⊩ psi -> T ⊩ psi.
  Proof.
    intros (A & HA1 & HA2) (B & HB1 & HB2) % prv_T_impl.
    use_theory (A ++ B). oimport HA2. oimport HB2. oapply 0. ctx.
  Qed.

  Lemma prv_T_comp T phi psi xi :
    T ⋄ phi ⊩ xi -> T ⋄ psi ⊩ phi -> T ⋄ psi ⊩ xi.
  Proof.
    intros (A & HA1 & HA2) % prv_T_impl (B & HB1 & HB2) % prv_T_impl.
    use_theory (psi :: A ++ B). oimport HA2. oimport HB2. oapply 1. oapply 0. ctx.
  Qed.

  Lemma elem_prv T phi :
    phi ∈ T -> T ⊩ phi.
  Proof.
    intros ?. use_theory [phi]. ctx.
  Qed.
End TheoryManipulation.

(* ** Refutation completeness *)

Section RefutationComp.
  Context {Sigma : Signature}.
  Context {HF : eq_dec Funcs} {HP : eq_dec Preds}.
  
  Lemma refutation_prv T phi :
    T ⊩CE phi <-> (T ⋄ ¬ phi) ⊩CE ⊥.
  Proof.
    split.
    - intros (A & HA1 & HA2). use_theory (¬ phi :: A). oimport HA2. oapply 1. ctx.
    - intros (A & HA1 & HA2) % prv_T_impl. use_theory A. now apply DN.
  Qed.
End RefutationComp.

(* ** Double Negation Translation *)

Section DNT.
  Context {Sigma : Signature}.

  Fixpoint dnt phi :=
    match phi with
    | ⊥ => ⊥
    | Pred P v => ¬ ¬ Pred P v
    | phi --> psi => dnt phi --> dnt psi
    | phi ∧ psi => dnt phi ∧ dnt psi
    | phi ∨ psi => ¬ (¬ dnt phi ∧ ¬ dnt psi)
    | ∀ phi => ∀ dnt phi
    | ∃ phi => ¬ ∀ ¬ dnt phi
    end.

  Lemma dnt_subst phi sigma :
    dnt (phi[sigma]) = (dnt phi)[sigma].
  Proof.
    induction phi in sigma |-*; comp; congruence.
  Qed.

  Lemma form_ind_subst' (P : form -> Prop) :
    P ⊥ -> (forall p v, P (Pred p v)) ->
    (forall phi psi, P phi -> P psi -> P (phi --> psi)) ->
    (forall phi psi, P phi -> P psi -> P (phi ∧ psi)) ->
    (forall phi psi, P phi -> P psi -> P (phi ∨ psi)) ->
    (forall phi,  P phi -> P (∀ phi)) ->
    (forall phi, (forall sigma, P phi[sigma]) -> P (∃ phi)) ->
    forall phi, P phi.
  Proof.
    intros H1 H2 H3 H4 H5 H6 H7 phi.
    induction phi using (@size_induction _ size).
    destruct phi; trivial.
    - apply H3; apply H; cbn; lia.
    - apply H4; apply H; cbn; lia.
    - apply H5; apply H; cbn; lia.
    - apply H6. eauto. 
    - apply H7. intros t. apply H.
      cbn. rewrite subst_size. lia.
  Qed.

  Lemma dnt_float A phi :
    A ⊢IE (¬ ¬ dnt phi) -> A ⊢IE dnt phi.
  Proof.
    intros Hprv. revert A Hprv. induction phi using form_ind_subst'; intros A Hprv. 1-7:comp.
    - eauto.
    - oimport Hprv. ointros. oapply 1. ointros. oapply 0. ctx.
    - oimport Hprv. ointros. apply IHphi2. ointros. oapply 2. ointros. oapply 1.
      oapply 0. ctx.
    - oimport Hprv. eapply CI.
      + eapply IHphi1. ointros.
        oapply 1. ointros. oapply 1. eapply CE1. ctx.
      + eapply IHphi2. ointros.
        oapply 1. ointros. oapply 1. eapply CE2. ctx.
    - oimport Hprv. ointros. oapply 1. ointros.
      oapply 0. ctx.
    - oimport Hprv. ointros. comp. apply IHphi. ointros. oapply 1.
      ointros. ospecialize 0 (var_term 0). oapply 2. ctx.
    - oimport Hprv. cbn. ointros. oapply 1. ointros.
      oapply 0. ctx.
  Qed.

  Ltac clean_dnt_correct :=
    repeat (match goal with
            | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
            end).
  
  Lemma dnt_to_IE A phi :
    A ⊢CE phi -> map dnt A ⊢IE dnt phi.
  Proof.
    remember expl; remember class; induction 1; subst; comp; eauto using in_map; clean_dnt_correct.
    - apply AllI. rewrite map_map in *. erewrite map_ext. apply IHprv. now setoid_rewrite <- dnt_subst.
    - apply AllE with (t0 := t) in IHprv. now rewrite dnt_subst.
    - ointros. ospecialize 0 t. oapply 0. rewrite dnt_subst in *. ouse IHprv.
    - oimport IHprv1. eapply dnt_float. ointros.
      oapply 1. ointros. oapply 1. rewrite dnt_subst in *. ouse IHprv2.
      intros ? [-> | (? & <- & ?) % in_map_iff]; eauto.
      eapply in_map_iff in H1 as (? & <- & ?).
      repeat right. eapply in_map_iff. exists (dnt x0). rewrite dnt_subst; eauto.      
    - ointros. eapply IE. eapply CE1. ctx. eapply Weak. eassumption. firstorder.
    - ointros. eapply IE. eapply CE2. ctx. eapply Weak. eassumption. firstorder.
    - oimport IHprv1. eapply dnt_float. ointros.
      oapply 1. osplit.
      + ointros. oapply 1. eapply Weak. eapply IHprv2. firstorder.
      + ointros. oapply 1. eapply Weak. eapply IHprv3. firstorder.
    - change (((dnt phi --> dnt psi) --> dnt phi) --> dnt phi) with (dnt (((phi --> psi) --> phi) --> phi)).
      apply dnt_float. comp. ointros. oapply 0. ointros. oapply 0. ointros. oexfalso. oapply 2.
      ointros. ctx.
  Qed.

  Lemma IE_to_CE A phi :
    A ⊢IE phi -> A ⊢CE phi.
  Proof.
    induction 1; eauto.
  Qed.
  
  Lemma dnt_CE A phi :
    A ⊢CE dnt phi <-> A ⊢CE phi.
  Proof.
    induction phi in A |-*; cbn in *.
    - reflexivity.
    - split. 1: eauto using DN. intros Hprv. ointros. oapply 0. ouse Hprv.
    - split; intros Hprv; oimport Hprv. all: ointros; apply IHphi2; oapply 1; apply IHphi1; ctx.
    - split; intros Hprv; oimport Hprv. all: osplit. 1,3: eapply IHphi1, CE1. 3,4: eapply IHphi2, CE2.
      all:ctx.      
    - split; intros Hprv; oimport Hprv.
      + oindirect. oapply 1. osplit.
        * ointros. oapply 1.  oleft. eapply IHphi1. ctx.
        * ointros. oapply 1. oright. eapply IHphi2. ctx.
      + ointros. eapply DE.
        * ctx.
        * eapply IE with (phi := dnt phi1). eapply CE1. ctx. eapply IHphi1. ctx.
        * eapply IE with (phi := dnt phi2). eapply CE2. ctx. eapply IHphi2. ctx.        
    - split; intros Hprv; oimport Hprv. all: ointros; apply IHphi; ospecialize 0 (var_term 0); ctx.
    - split; intros Hprv; oimport Hprv.
      + oindirect. oapply 1. ointros. oapply 1.
        eapply ExI with (t := var_term 0). asimpl. eapply IHphi. ctx.
      + ointros. eapply ExE. ctx. cbn.
        ospecialize 1 (var_term 0). oapply 0. eapply IHphi. ctx.
  Qed.

  Lemma dnt_remove_ctx A B phi :
    (A ++ map dnt B) ⊢CE phi -> (A ++ B) ⊢CE phi.
  Proof.
    induction B in A |-*; cbn.
    - now rewrite app_nil_r.
    - intros H. specialize (IHB (A ++ [a])). do 2 rewrite <- app_assoc in IHB. apply IHB.
      apply prv_cut with (dnt a). 1: apply dnt_CE; ctx; intuition. apply (Weak H).
      intros ? [| []] % in_app_or; subst; intuition. repeat (right; apply in_or_app). now right.
  Qed.

  Lemma dnt_to_CE A phi :
    map dnt A ⊢IE dnt phi -> A ⊢CE phi.
  Proof.
    intros H % IE_to_CE. now apply dnt_remove_ctx with (A := nil), dnt_CE.
  Qed.
End DNT.
