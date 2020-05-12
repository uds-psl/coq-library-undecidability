(** ** Natural Deduction for FOL* *)

From Undecidability.FOLC Require Export FOL.

Section ND_def.
  Context {Sigma : Signature}.

  (* **** Definition *)

  Inductive peirce := class | intu.
  Inductive bottom := expl | lconst.
  Existing Class peirce.
  Existing Class bottom.

  Inductive prv : forall (p : peirce) (b : bottom), list (form) -> form -> Prop :=
  | II {p b} A phi psi : prv p b (phi::A) psi -> prv p b A (phi --> psi)
  | IE {p b} A phi psi : prv p b A (phi --> psi) -> prv p b A phi -> prv p b A psi
  | AllI {p b} A phi : prv p b (map (subst_form ↑) A) phi -> prv p b A (∀ phi)
  | AllE {p b} A phi t : prv p b A (All phi) -> prv p b A (subst_form (t .: ids) phi)
  | Exp {p} A phi : prv p expl A Fal -> prv p expl A phi
  | Pc {b} A phi psi : prv class b A (((phi --> psi) --> phi) --> phi)
  | Ctx {p b} A phi : phi el A -> prv p b A phi.
  Arguments prv {_ _} _ _.

  Hint Constructors prv.

  Notation "A ⊢ phi" := (prv A phi) (at level 30).
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
      induction 1 in B |-*; eauto using incl_map.
    Qed.

    Theorem subst_Weak A phi xi :
      A ⊢ phi -> [phi[xi] | phi ∈ A] ⊢ phi[xi].
    Proof.
      induction 1 in xi |-*; comp; eauto using in_map.
      - apply AllI. setoid_rewrite map_map in IHprv. erewrite map_map, map_ext.
        apply IHprv. intros ?. comp. now apply ext_form.
      - specialize (IHprv xi). apply AllE with (t0 := t [xi]) in IHprv. comp. now asimpl in IHprv.
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
        assumption. intuition comp. erewrite ext_form. asimpl. reflexivity. intros []; now asimpl.
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

(* **** Proof Tacticts *)

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
  eapply prv_cut; [eapply (@AllE _ _ _ _ _ t); ctx_index n|]; cbn; asimpl.

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

Lemma DN_T {Sigma : Signature} T phi :
  T ⊩CE ¬ (¬ phi) -> T ⊩CE phi.
Proof.
  intros (A & HA1 & HA2 % DN). now use_theory A.
Qed.

Ltac oindirect := apply DN, II.

Lemma ExE {Sigma : Signature} A phi psi :
  A ⊢CE (∃ phi) -> (phi :: [phi[↑] | phi ∈ A]) ⊢CE psi[↑] -> A ⊢CE psi.
Proof.
  intros Hex Hinst.
  oindirect. oimport Hex. oapply 0.
  ointros. oapply 2. ouse Hinst.
Qed.

Ltac odestruct n := eapply ExE; [ctx_index n|]; cbn; asimpl.

Lemma ExI {Sigma : Signature} {p : peirce} {b : bottom} A t phi :
  A ⊢ phi [t..] -> A ⊢ ∃ phi.
Proof.
  intros Hc. apply II. ospecialize 0 t. oapply 0. ouse Hc.
Qed.

Ltac oexists t :=
  eapply (@ExI _ _ _ _ t); cbn; asimpl.

Lemma AXM {Sigma : Signature} A phi psi :
  (phi :: A) ⊢CE psi -> (¬ phi :: A) ⊢CE psi -> A ⊢CE psi.
Proof.
  intros Ht Hf. oindirect. oassert (¬ phi). ointros. oapply 1.
  ouse Ht. oapply 1. ouse Hf.
Qed.

Ltac oxm form :=
  apply (@AXM _ _ form).

Lemma DP {Sigma : Signature} phi :
  [] ⊢CE ∃ (phi --> (∀ phi)[↑]).
Proof.
  oxm (∃ ¬ phi).
  - odestruct 0. oexists (var_term 0). ointros. oexfalso. oapply 1. ctx.
  - oexists (var_term 0). ointros. oindirect. oapply 2. oexists (var_term 0). ctx.
Qed.

(* **** Theory manipulation *)

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

(* **** Refutation completeness *)

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

(* **** Enumerability of proofs *)

Section Enumerability.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Fixpoint L_ded {p : peirce} {b : bottom} (A : list form) (n : nat) : list form :=
    match n with
    | 0 => A
    | S n =>   L_ded A n ++
    (* II *)   concat ([ [ phi --> psi | psi ∈ L_ded (phi :: A) n ] | phi ∈ L_T form n ]) ++
    (* IE *)   [ psi | (phi, psi) ∈ (L_ded A n × L_T form n) , (phi --> psi el L_ded A n) ] ++
    (* AllI *) [ ∀ phi | phi ∈ L_ded (map (subst_form ↑) A) n ] ++
    (* AllE *) [ phi[t..] | (phi, t) ∈ (L_T form n × L_T term n), (∀ phi) el L_ded A n ] ++
    (* Exp *)  (if b then
                [ phi | phi ∈ L_T form n, ⊥ el L_ded A n]
                else nil) ++
    (* Pc *)   (if p then
                [ (((phi --> psi) --> phi) --> phi) | (pair phi psi) ∈ (L_T form n × L_T form n)]
                else nil)
    end.

  Opaque in_dec.

  Lemma enum_prv {p : peirce} {b : bottom} A : enum (prv A) (L_ded A).
  Proof with try (eapply cum_ge'; eauto; omega).
    repeat split.
    - eauto.
    - rename x into phi. induction 1; try congruence; subst.
      + destruct IHprv as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 2.
        eapply in_concat_iff. eexists. split. 2:in_collect phi... in_collect psi...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T psi) as [m3]; eauto.
        exists (1 + m1 + m2 + m3).
        cbn. in_app 3. in_collect (phi, psi)...
      + destruct IHprv as [m]. exists (1 + m). cbn. in_app 4. in_collect phi...
      + destruct IHprv as [m1], (el_T t) as [m2], (el_T phi) as [m3]. exists (1 + m1 + m2 + m3).
        cbn. in_app 5. in_collect (phi, t)...
      + destruct IHprv as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 6. in_collect phi...
      + destruct (el_T phi) as [m1], (el_T psi) as [m2]. exists (1 + m1 + m2). cbn. in_app 7. in_collect (phi, psi)...
      + now exists 0.
    - intros [m]; induction m in A, x, H |-*; cbn in *.
      + ctx.
      + destruct p, b; inv_collect; eauto. all: apply AllE; eauto.
  Qed.

  Fixpoint L_con (L : nat -> list form) (n : nat) : list (list form) :=
    match n with
    | 0 => [ nil ]
    | S n => L_con L n ++ [ phi :: A | (pair phi A) ∈ (L n × L_con L n) ]
    end.

  Lemma enum_el X (p : X -> Prop) L x :
    enum p L -> p x -> exists m, x el L m.
  Proof.
    firstorder.
  Qed.
  Arguments enum_el {X p L} x _ _.

  Lemma enum_p X (p : X -> Prop) L x m :
    enum p L -> x el L m -> p x.
  Proof.
    firstorder.
  Qed.

  Lemma enum_containsL T L : enum T L -> enum (fun A => A ⊏ T) (L_con L).
  Proof with try (eapply cum_ge'; eauto; omega).
    intros He. repeat split.
    - eauto.
    - induction x as [| phi A]; intros HT.
      + exists 0. firstorder.
      + destruct IHA as [m1], (enum_el phi He) as [m2]. 1,2,3: firstorder.
        exists (1 + m1 + m2). cbn. in_app 2. destruct He. in_collect (phi, A)...
    - intros [m]. induction m in x, H |-*; cbn in *.
      + destruct H as [<- | []]. intuition.
      + inv_collect. apply IHm in H1. apply (enum_p He) in H. eauto with contains_theory.
  Qed.

  Fixpoint L_tded {p : peirce} {b : bottom} (L : nat -> list form) (n : nat) : list form :=
    match n with
    | 0 => nil
    | S n => L_tded L n ++ concat ([ L_ded A n | A ∈ L_con L n ])
    end.

  Lemma enum_tprv {p : peirce} {b : bottom} T L : enum T L -> enum (tprv T) (L_tded L).
  Proof with try (eapply cum_ge'; eauto; omega).
    intros He. repeat split.
    - eauto.
    - intros (A & [m1] % (enum_el A (enum_containsL He)) & [m2] % (enum_el x (enum_prv A))).
      exists (1 + m1 + m2). cbn. in_app 2. eapply in_concat_iff. eexists. split. 2: in_collect A... idtac...
    - intros [m]. induction m in x, H |-*; cbn in *. 1: contradiction. inv_collect. exists x1. split.
      + eapply (enum_p (enum_containsL He)); eassumption.
      + eapply (enum_p (enum_prv x1)); eassumption.
  Qed.
End Enumerability.

(* **** Signature extension and proofs *)

Section SigExt.
  Context {p : peirce} {b : bottom}.

  Lemma sig_lift_Weak {Sigma : Signature} A phi :
    A ⊢ phi -> (map sig_lift A) ⊢ sig_lift phi.
  Proof.
    destruct Sigma. induction 1; try (solve [cbn in *; constructor; eauto using in_map]).
    - eapply IE; cbn in *; eauto.
    - constructor. rewrite map_map in *. erewrite map_ext. 1: exact IHprv. now setoid_rewrite sig_lift_subst.
    - rewrite sig_lift_subst. apply @AllE with (t := sig_lift_term t) in IHprv. erewrite ext_form. exact IHprv.
      now intros [].
  Qed.

  Lemma vsubs_form_shift {Sigma : Signature} x :
    form_shift x = vsubs 1 Vector.nil x.
  Proof.
    unfold vsubs. destruct (fin_minus x 0). 1: omega. destruct s; subst. now replace (x - 0 + 1) with (S x) by omega.
  Qed.

  Lemma vsubs_single_subst {Sigma : Signature} (t : term) x :
    (t..) x = vsubs 0 (Vector.cons t Vector.nil) x.
  Proof.
    destruct x. 1: reflexivity. unfold vsubs. destruct (fin_minus (S x) 1).
    1: omega. destruct s; subst. now replace (S x - 1 + 0) with x by omega.
  Qed.

  Lemma sig_drop_Weak {Sigma : Signature} n A phi :
    A ⊢ phi -> map (sig_drop n) A ⊢ sig_drop n phi.
  Proof with solve [eauto] + firstorder + (intros ? []; subst; firstorder).
    destruct Sigma. induction 1 in n |-*; try (solve [cbn in *; constructor; eauto using in_map]).
    - eapply IE. 1: apply IHprv1. apply IHprv2.
    - comp. apply AllI. specialize (IHprv (S n)). setoid_rewrite map_map in IHprv. rewrite map_map.
      erewrite map_ext in IHprv. 2: intros a; erewrite ext_form with (s := a). 3: apply vsubs_form_shift.
      2: replace (S n) with (n + 1) by omega; rewrite sig_drop_subst'.
      2: erewrite ext_form with (s := sig_drop' (n + 0) a). 3: intros x; symmetry; apply vsubs_form_shift.
      2: replace (n + 0) with n by omega; reflexivity. assumption.
    - comp. specialize (IHprv n). apply @AllE with (t := sig_drop_term' n t) in IHprv.
      erewrite @ext_form with (s := sig_drop' (S n) phi) in IHprv. 2: apply vsubs_single_subst.
      replace (S n) with (n + 1) in IHprv by omega. 
      change (Vector.cons (sig_drop_term' n t) Vector.nil) with (Vector.map (sig_drop_term' n) (Vector.cons t Vector.nil)) in IHprv.
      replace (sig_drop_term' n) with (@sig_drop_term' Funcs fun_ar Preds pred_ar (n + 0)) in IHprv by (f_equal; omega).
      rewrite <- sig_drop_subst' in IHprv. erewrite ext_form with (s := phi) in IHprv. 2: intros; symmetry; apply vsubs_single_subst.
      replace (n + 0) with n in IHprv by omega. apply IHprv.
  Qed.

  Lemma sig_lift_out {Sigma : Signature} (A : list form) (phi : form) :
    @prv (sig_ext Sigma) _ _ (map (fun psi => (sig_lift psi)[@ext_c Sigma]) A) ((sig_lift phi)[@ext_c Sigma]) -> A ⊢ phi.
  Proof.
    intros H % (sig_drop_Weak 0). setoid_rewrite lift_drop_inverse in H. rewrite map_map in H. erewrite map_ext in H.
    2: apply lift_drop_inverse. now rewrite map_id in H.
  Qed.

  Lemma sig_lift_out_T {Sigma : Signature} (T : theory) (phi : form) :
    @tprv (sig_ext Sigma) _ _ (tmap (fun psi => (sig_lift psi)[@ext_c Sigma]) T) ((sig_lift phi)[@ext_c Sigma]) -> T ⊩ phi.
  Proof.
    intros (A & HA1 & HA2). enough (exists C, C ⊏ T /\ A = (map (fun psi => (sig_lift psi)[@ext_c Sigma]) C)) as (C & HC1 & HC2).
    1: subst; use_theory C; exact (sig_lift_out HA2). clear HA2. induction A. 1: exists nil; cbn; firstorder.
    destruct IHA as (C & HC1 & HC2). 1: firstorder. destruct (HA1 a (or_introl eq_refl)) as (c & Hc1 & Hc2). use_theory (c :: C). now subst.
  Qed.
End SigExt.

(* **** Double Negation Translation *)

Section DNT.
  Context {Sigma : Signature}.

  Fixpoint dnt phi :=
    match phi with
    | ⊥ => ⊥
    | Pred P v => ¬ ¬ Pred P v
    | phi --> psi => dnt phi --> dnt psi
    | ∀ phi => ∀ dnt phi
    end.

  Lemma dnt_subst phi sigma :
    dnt (phi[sigma]) = (dnt phi)[sigma].
  Proof.
    induction phi in sigma |-*; comp; congruence.
  Qed.

  Lemma dnt_float A phi :
    A ⊢IE (¬ ¬ dnt phi) -> A ⊢IE dnt phi.
  Proof.
    intros Hprv. induction phi in A, Hprv |-*; comp.
    - eauto.
    - oimport Hprv. ointros. oapply 1. ointros. oapply 0. ctx.
    - oimport Hprv. ointros. apply IHphi2. ointros. oapply 2. ointros. oapply 1.
      oapply 0. ctx.
    - oimport Hprv. ointros. comp. apply IHphi. ointros. oapply 1.
      ointros. ospecialize 0 (var_term 0). oapply 2. ctx.
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
    - apply AllE with (t0 := t) in IHprv. now setoid_rewrite dnt_subst.
    - change (((dnt phi --> dnt psi) --> dnt phi) --> dnt phi) with (dnt (((phi --> psi) --> phi) --> phi)).
      apply dnt_float. comp. ointros. oapply 0. ointros. oapply 0. ointros. oexfalso. oapply 2.
      ointros. ctx.
  Qed.

  Lemma dnt_to_TIE T phi :
    T ⊩CE phi -> tmap dnt T ⊩IE dnt phi.
  Proof.
    intros (A & HA1 & HA2 % dnt_to_IE). use_theory [dnt p | p ∈ A]. 2: assumption.
    intros ? (psi & <- & ?) % in_map_iff. exists psi. firstorder.
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
    - split; intros Hprv; oimport Hprv. all: ointros; apply IHphi; ospecialize 0 (var_term 0); ctx.
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

  Lemma dnt_to_TCE T phi :
    tmap dnt T ⊩IE dnt phi -> T ⊩CE phi.
  Proof.
    intros (? & (A & -> & HA1) % tmap_contains_L & HA2 % dnt_to_CE). now use_theory A.
  Qed.
End DNT.
