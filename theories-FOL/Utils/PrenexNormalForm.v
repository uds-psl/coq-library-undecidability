(* * Prenex Normal Form *)
From FOL Require Import FullSyntax Arithmetics.
Require Import Lia Vector List.
Import Vector.VectorNotations.
Import List.ListNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.

Section PNFrules.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {D: Type} {i: interp D}.

  Definition DN := forall P, ~~P -> P.
  Definition IndependenceOfGeneralPremises :=
    forall (d : D) (P:D -> Prop) (Q:Prop),
      (Q -> exists x, P x) -> exists x, (Q -> P x).
  
  Lemma DN_to_IndependenceOfGeneralPremises :
    DN -> IndependenceOfGeneralPremises.
  Proof. intros DN. unfold IndependenceOfGeneralPremises.
        intros d P Q H. apply DN. intros nH. apply nH.
        exists d. intros q. exfalso. apply nH.
        specialize (H q) as [x Px]. now exists x.
  Qed.
  
  Lemma up_equiv {b:falsity_flag}:
    forall ρ ϕ x, sat ρ ϕ <-> sat (x.:ρ) ϕ[↑].
  Proof.
    intros. split.
    - intros. apply sat_comp. eapply sat_ext; eauto.
    - intros H%sat_comp. eapply sat_ext; eauto.
  Qed.

  Lemma PNF_allAnd {b:falsity_flag}:
    forall ρ ϕ ψ, sat ρ ((∀ ϕ) ∧ ψ ↔ ∀ ϕ ∧ ψ[↑]).
  Proof.
    split; cbn.
    - intros []. split; [auto | now apply up_equiv].
    - intros H. split.
      + intros. now specialize (H d) as [H1 H2%sat_comp].
      + destruct (H (ρ 42)). eapply up_equiv, H1.
  Qed.

  Lemma PNF_andAll {b:falsity_flag}:
    forall ρ ϕ ψ, sat ρ (ϕ ∧ (∀ ψ) ↔ ∀ ϕ[↑] ∧ ψ).
  Proof.
    intros ρ ϕ ψ. specialize (PNF_allAnd ρ ψ ϕ) as H. cbn in *. firstorder.
  Qed.

  Lemma PNF_all_Or1 {b:falsity_flag}:
    forall ρ ϕ ψ, sat ρ ((∀ ϕ) ∨ ψ → ∀ ϕ ∨ ψ[↑]).
  Proof.
    cbn.
    intros ρ ϕ ψ [] d.
    + now left.
    + right. now apply up_equiv.
  Qed.

  Lemma PNF_all_Or2 {b:falsity_flag}:
    DN -> forall ρ ϕ ψ, sat ρ ((∀ ϕ ∨ ψ[↑]) → ((∀ ϕ) ∨ ψ)) .
  Proof.
    cbn. intros DN ρ ϕ ψ H. (* TODO vlt. de Morgan = wxm*)
      apply DN. intros nH. apply nH. left. intros d. specialize (H d) as [H | H].
        + auto.
        + exfalso. apply nH. right. eapply up_equiv, H.
  Qed.

  Lemma PNF_allOr {b:falsity_flag}:
    DN -> forall ρ ϕ ψ, sat ρ (((∀ ϕ) ∨ ψ) ↔ (∀ ϕ ∨ ψ[↑])).
  Proof.
    intros DN. split; [apply PNF_all_Or1|apply PNF_all_Or2, DN].
  Qed.

  Lemma PNF_orAll {b:falsity_flag}:
    DN -> forall ρ ϕ ψ, sat ρ ((ϕ ∨ (∀ψ) ↔ (∀ ϕ[↑] ∨ ψ))).
  Proof.
    intros DN ρ ϕ ψ. specialize (PNF_allOr DN ρ ψ ϕ) as H. cbn in *. revert H. clear. firstorder.
  Qed.

  Lemma PNF_existsAnd {b:falsity_flag}:
    forall ρ ϕ ψ, sat ρ (((∃ ϕ) ∧ ψ) ↔ (∃ ϕ ∧ ψ[↑])).
  Proof.
    split; cbn.
    - intros [[]]. eexists. split; [eauto | now apply up_equiv].
    - intros [? []]. split; [|eapply up_equiv]; eauto.
  Qed.

  Lemma PNF_andExists {b: falsity_flag}:
    forall ρ ϕ ψ, sat ρ ((ϕ ∧ ∃ ψ) ↔ (∃ ϕ[↑] ∧ ψ)).
  Proof.
    intros ρ ϕ ψ. specialize (PNF_existsAnd ρ ψ ϕ) as H. cbn in *. revert H. clear. firstorder.
  Qed.

  Lemma PNF_existsOr {b:falsity_flag}:
    forall ρ ϕ ψ, sat ρ ((∃ ϕ) ∨ ψ ↔ ∃ ϕ ∨ ψ[↑]).
  Proof.
    split; cbn.
    - intros [[d H]|H].
      + exists d. now left.
      + exists (ρ 1337). right. now apply up_equiv.
    - intros [d [H|H]].
      + left. eauto.
      + right. eapply up_equiv, H.
  Qed.

  Lemma PNF_orExists {b:falsity_flag}:
    forall ρ ϕ ψ, sat ρ (ϕ ∨ (∃ ψ) ↔ ∃ ϕ[↑] ∨ ψ).
  Proof.
    intros ρ ϕ ψ. specialize (PNF_existsOr ρ ψ ϕ) as H. cbn in *. revert H. clear. firstorder.
  Qed.

  Lemma PNF_allImpl1 {b: falsity_flag}:
    DN -> forall ρ ϕ ψ, sat ρ (((∀ ϕ) → ψ) → (∃ ϕ → ψ[↑])).
  Proof.
    cbn.
    intros DN ρ ϕ ψ A. apply DN. intros nE.
    apply nE. exists (ρ 27). intros H. apply up_equiv. apply A. intros d.
    apply DN. intros nH. apply nE. exists d. contradiction.
  Qed.

  Lemma PNF_allImpl2 {b: falsity_flag}:
    forall ρ ϕ ψ, sat ρ ((∃ ϕ → ψ[↑]) → ((∀ ϕ) → ψ)).
  Proof.
    cbn. intros ? ? ? [] ?. eapply up_equiv. eauto.
  Qed.

  Lemma PNF_allImpl {b: falsity_flag}:
    DN -> forall ρ ϕ ψ, sat ρ (((∀ ϕ) → ψ) ↔ (∃ ϕ → ψ[↑])).
  Proof.
    intros DN. split; [apply PNF_allImpl1, DN| apply PNF_allImpl2].
  Qed.

  Lemma PNF_existsImpl {b: falsity_flag}:
    forall ρ ϕ ψ, sat ρ (((∃ ϕ) → ψ) ↔ (∀ ϕ → ψ[↑])).
  Proof.
    split; cbn.
    - intros. apply up_equiv. eauto.
    - intros ? []. eapply up_equiv. eauto.
  Qed.

  Lemma PNF_implAll {b: falsity_flag}:
    forall ρ ϕ ψ, sat ρ ((ϕ → ∀ ψ) ↔ (∀ ϕ[↑] → ψ)).
  Proof.
    split; cbn.
    - intros ? ? ?%up_equiv. auto.
    - intros H ? d. apply H. now apply up_equiv.
  Qed.

  Lemma PNF_implExists {b: falsity_flag}:
  IndependenceOfGeneralPremises -> forall ρ ϕ ψ, sat ρ ((ϕ → ∃ ψ) ↔ ∃ ϕ[↑] → ψ).
  Proof.
    intros IndependenceOfGeneralPremises.
    split; cbn. (* todo indepentence of premise *) (* markov **)
    - intros H.
      assert (exists d : D, ((forall d, (d .: ρ) ⊨ ϕ[↑]) -> (d .: ρ) ⊨ ψ)) as [d H']. {
        apply (IndependenceOfGeneralPremises (ρ 42)).
        intros H'. apply H. specialize (H' (ρ 27)). apply sat_comp in H'.
          eapply sat_ext. 2: exact H'. reflexivity.
      }
      exists d. intros H''. apply H'. intros d'. apply sat_comp. apply sat_comp in H''.
      eapply sat_ext. 2: exact H''. reflexivity.
    - intros [d H] ?. eexists. apply H. now apply up_equiv.
  Qed.

  Lemma equivTrans {ff: falsity_flag} ρ a b c :
    ρ ⊨ (a ↔ b) -> ρ ⊨ (c ↔ b) -> ρ ⊨ (a ↔ c).
  Proof. firstorder. Qed.

  Lemma equivToCoq {ff: falsity_flag} ρ a b :
    ρ ⊨ (a ↔ b) -> ρ ⊨ a <-> ρ ⊨ b.
  Proof. firstorder. Qed.

  Lemma PNF_notExists:
    forall ρ ϕ, sat ρ ((¬∃ ϕ) ↔ (∀ ¬ϕ)).
  Proof.
    intros ? ?.
    eapply equivTrans; [apply PNF_existsImpl | now cbn].
  Qed.

  Lemma PNF_notAll:
    DN -> forall ρ ϕ, sat ρ (¬∀ ϕ) <-> sat ρ (∃ ¬ϕ).
  Proof.
    intros DN ? ?.
    eapply equivTrans; [apply (PNF_allImpl DN) | now cbn].
  Qed.
  
End PNFrules.

Section PrenexNormalForm.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {D: Type} {i: interp D}.

  Fixpoint noQuant_bool `{falsity_flag} (f: form) : bool :=
    match f with
    | falsity => true
    | atom P v => true
    | bin op ϕ1 ϕ2 => noQuant_bool ϕ1 && noQuant_bool ϕ2
    | quant op ϕ => false
    end.

  Fixpoint isPNF_bool `{falsity_flag} (f: form) : bool :=
    match f with
    | falsity => true
    | atom P v => true
    | bin op ϕ1 ϕ2 => noQuant_bool ϕ1 && noQuant_bool ϕ2
    | quant op ϕ => isPNF_bool ϕ
    end.

  Inductive noQuant_ind : forall b, form b -> Prop :=
  | nQ_false : noQuant_ind falsity
  | nQ_atom {b} P v : noQuant_ind ((atom P v): form b)
  | nQ_bin {b} op (ϕ1 ϕ2: form b) : noQuant_ind ϕ1 -> noQuant_ind ϕ2 -> noQuant_ind (bin op ϕ1 ϕ2).

  Inductive PNF_ind : forall b, form b -> Prop :=
  | PNF_noQuant {b} ϕ : @noQuant_ind b ϕ -> PNF_ind ϕ
  | PNF_quant {b} op (ϕ: form b) : PNF_ind ϕ -> PNF_ind (quant op ϕ).

  #[local] Hint Constructors noQuant_ind : core.
  #[local] Hint Constructors PNF_ind : core.

  Lemma noQuand_ind_inv {ff: falsity_flag} {ϕ} (nQ : noQuant_ind ϕ) :
    match ϕ with
    | bin op φ1 φ2 => noQuant_ind φ1 /\ noQuant_ind φ2 
    | quant _ _ => False
    | _ => True
    end.
  Proof.
    induction nQ; easy.
  Qed.

  Lemma PNF_ind_inversion {ff: falsity_flag} {ϕ} (pnf : PNF_ind ϕ) :
    match ϕ with
    | quant op φ => PNF_ind φ
    | _ => noQuant_ind ϕ
    end.
  Proof.
    induction pnf; destruct ϕ; easy.
  Qed.

  Fixpoint noQuant_ind_rec 
    (P : forall b : falsity_flag, form -> Type)
    (H0 : P falsity_on ⊥)
    (H1 : forall (b : falsity_flag) (P0 : Σ_preds) (v : vec term (ar_preds P0)), P b (atom P0 v : form))
    (H2 : forall (b : falsity_flag) (op : binop) (ϕ1 ϕ2 : form), noQuant_ind ϕ1 -> P b ϕ1 -> noQuant_ind ϕ2 -> P b ϕ2 -> P b (bin op ϕ1 ϕ2))
    {b : falsity_flag} (f : form) (nQ : noQuant_ind f)
    : P b f.
  Proof.
    destruct f.
    - apply H0.
    - apply H1.
    - apply H2.
      + now destruct (noQuand_ind_inv nQ).
      + apply noQuant_ind_rec; try assumption. now destruct (noQuand_ind_inv nQ).
      + now destruct (noQuand_ind_inv nQ).
      + apply noQuant_ind_rec; try assumption. now destruct (noQuand_ind_inv nQ).
    - now destruct (noQuand_ind_inv nQ).
  Defined.

  Fixpoint PNF_ind_rec
    (P : forall b : falsity_flag, form -> Type)
    (H0 : forall (b : falsity_flag) (ϕ : form), noQuant_ind ϕ -> P b ϕ)
    (H1 : forall (b : falsity_flag) (op : quantop) (ϕ : form), PNF_ind ϕ -> P b ϕ -> P b (quant op ϕ))
    {b : falsity_flag} (f : form) (p : PNF_ind f) 
    : P b f.
  Proof.
    destruct f.
    - apply H0. constructor.
    - apply H0. now constructor.
    - apply H0. apply (PNF_ind_inversion p).
    - apply PNF_ind_inversion in p.
      apply H1.
      + assumption.
      + now apply PNF_ind_rec.
  Defined.

  Lemma noQuant_agree (b: falsity_flag) (ϕ: form b):
    noQuant_ind ϕ <-> noQuant_bool ϕ = true.
  Proof.
    split.
    - intros nQi. induction nQi as [|b P v|b op ϕ1 ϕ2 nQi1 IH1 nQi2 IH2].
      + cbn. reflexivity.
      + cbn. reflexivity.
      + cbn. rewrite IH1, IH2. reflexivity.
    - induction ϕ as [|b P v|b op ϕ1 IH1 ϕ2 IH2|]; cbn in *.
      + constructor.
      + constructor.
      + destruct (noQuant_bool ϕ1), (noQuant_bool ϕ2); constructor; auto.
      + intros [=].
  Qed.

  Lemma PNF_agree (b: falsity_flag) (ϕ: form b):
    PNF_ind ϕ <-> isPNF_bool ϕ = true.
  Proof.
    induction ϕ as [|b P v|b op ϕ1 IH1 ϕ2 IH2|b op ϕ IHϕ]; cbn in *; split.
    - reflexivity.
    - econstructor. constructor.
    - reflexivity.
    - econstructor. constructor.
    - intros H.
      destruct (noQuand_ind_inv (PNF_ind_inversion H)).
      apply andb_true_intro. split; now apply noQuant_agree.
    - intros []%andb_prop. constructor. constructor; now apply noQuant_agree.
    - intros H. apply PNF_ind_inversion in H. now apply IHϕ.
    - intros. apply PNF_quant. now apply IHϕ.
  Qed.

  (** convert PNF definiton ***)
  Notation upN := (iter up) (only parsing).

  Notation shift k := (iter S k >> var).
  Definition shift_quant n k := upN n (shift k).

  Lemma iter_add_S a : iter S a = Nat.add a.
  Proof.
    induction a.
    - easy.
    - cbn. now rewrite IHa.
  Qed.

  Lemma upNup sig n :
    upN n (up sig) = up (upN n sig).
  Proof.
    now rewrite iter_switch.
  Qed.

  Lemma upN_explicit n sig j :
    upN n sig j = if Compare_dec.lt_dec j n then $j else (sig (j - n))`[shift n].
  Proof.
    destruct Compare_dec.lt_dec as [lt | geq].
    - induction j in lt, n |-*.
      + destruct n as [|n]; [lia|]. now cbn.
      + destruct n as [|n]; [lia|]. cbn.
        unfold funcomp. now rewrite IHj by lia.
    - induction n as [|n IH] in geq, j |-*.
      + replace (j - 0) with j by lia. now asimpl.
      + destruct j.
        * lia.
        * cbn. unfold funcomp. rewrite IH by lia. now asimpl.
  Qed.

  Lemma shift_quant_explicit n k j :
    shift_quant n k j = if Compare_dec.lt_dec j n then $j else $(k + j).
  Proof.
    unfold shift_quant.
    rewrite upN_explicit.
    destruct Compare_dec.lt_dec.
    - reflexivity.
    - cbn. unfold shift. f_equal. repeat rewrite iter_add_S. lia.
  Qed.

  Goal forall x, upN 4 (shift 38) x = ($0 .: $1 .: $2 .: $3 .: (shift 42)) x.
    unfold scons, funcomp. cbn.
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    destruct x; [reflexivity|].
    reflexivity.
  Qed.

  Open Scope list_scope.

  Fixpoint swap_quant (qs: list full_logic_quant): list full_logic_quant :=
    match qs with
    | [] => []
    | q::qs =>
      match q with
      | All => Ex::(swap_quant qs)
      | Ex => All::(swap_quant qs)
      end
    end.

  Fixpoint quant_list_to_form `{falsity_flag} (qs : list full_logic_quant) (f : form) : form :=
    match qs with
      | [] => f
      | q::qs => @quant _ _ full_operators _ q (quant_list_to_form qs f)
    end.

  Fixpoint conv_list `{falsity_flag} (f: form) : list full_logic_quant :=
    match f with
    | falsity => []
    | atom P v => []
    | bin op ϕ1 ϕ2 =>
      match op with
      | Impl => (swap_quant (conv_list ϕ1)) ++ (conv_list ϕ2)
      | _ => (conv_list ϕ1) ++ (conv_list ϕ2)
      end
    | quant op φ => op::(conv_list φ)
    end.

  Fixpoint conv_form `{falsity_flag} (f: form) : form :=
    match f with
    | falsity => falsity
    | atom P v => atom P v
    | bin op φ1 φ2 =>
        bin op
          ((conv_form φ1)[shift (length (conv_list φ2))])
          ((conv_form φ2)[shift_quant (length (conv_list φ2)) (length (conv_list φ1))])
    | quant op φ => conv_form φ
    end.

  Definition convert_PNF `{falsity_flag} (f : form) : form :=
    quant_list_to_form (conv_list f) (conv_form f).

  (** prove result is in PNF ***)

  Lemma noQuant_ind_subst `{falsity_flag} : 
    forall φ s, noQuant_ind φ -> noQuant_ind φ[s].
  Proof.
    intros φ s. induction 1; cbn; now constructor.
  Qed.

  Lemma conv_form_noQuant `{falsity_flag} φ :
    noQuant_ind (conv_form φ).
  Proof.
    induction φ as [|b P v|b op ϕ1 IH1 ϕ2 IH2|b op ϕ IHφ]; cbn.
    - constructor.
    - constructor.
    - destruct op; constructor; now apply noQuant_ind_subst.
    - exact IHφ.
  Qed.

  Lemma list_noQuant_PNF `{b: falsity_flag} qs ϕ :
    noQuant_ind ϕ -> PNF_ind (quant_list_to_form qs ϕ).
  Proof.
    induction qs as [|q qs].
    - now constructor.
    - intros H. cbn. apply PNF_quant. auto.
  Qed.

  Lemma convert_PNF_PNF `{falsity_flag} : forall ϕ, PNF_ind (convert_PNF ϕ).
  Proof.
    intros ϕ. unfold convert_PNF.
    apply list_noQuant_PNF, conv_form_noQuant.
  Qed.

  (** prove result in PNF is equivilant ***)

  Lemma quant_list_to_form_equiv {b: falsity_flag} qs ϕ1 ϕ2:
    (forall ρ, sat ρ ϕ1 <-> sat ρ ϕ2) -> forall ρ, sat ρ (quant_list_to_form qs ϕ1) <-> sat ρ (quant_list_to_form qs ϕ2).
  Proof.
    induction qs as [|[] ? ?]; firstorder.
  Qed.

  Lemma shift_one_more {b: falsity_flag} φ n :
    φ[shift (S n)] = φ[↑][shift n].
  Proof.
    asimpl. apply subst_ext. intros m. unfold shift, funcomp.
    now rewrite iter_switch.
  Qed.

  Lemma shift_quant_0 n : feq (shift_quant n 0) var.
  Proof.
    unfold shift_quant. intros x.
    enough (forall sigma, (forall x, sigma x = $x) -> (forall x, upN n sigma x = $x)) by auto.
    induction n.
    - now intros.
    - intros sig Hsig. cbn. rewrite iter_switch.
      apply IHn. unfold up.
      unfold scons. intros [|y]; [reflexivity|].
      unfold funcomp. now rewrite Hsig.
  Qed.

  Lemma shift_quant_add n a b x :
    (shift_quant n a x)`[shift_quant n b] = shift_quant n (a+b) x.
  Proof.
  unfold shift_quant, shift. induction n in a,b,x|-*.
  - cbn. f_equal. rewrite !iter_add_S. lia.
  - destruct x as [|x].
    + easy.
    + cbn. unfold funcomp at 3. rewrite <- IHn.
      rewrite !iter_add_S. unfold funcomp. rewrite !subst_term_comp.
      easy.
  Qed.

  Lemma shift_quant_1 {b: falsity_flag} φ n m:
    φ[shift_quant n 1][shift_quant n m] =
    φ[shift_quant n (S m)].
  Proof.
    asimpl. apply subst_ext.
    intros p. unfold funcomp. apply shift_quant_add.
  Qed.

  Lemma quant_list_to_form_rename_free {b: falsity_flag} sigma qs φ:
  quant_list_to_form qs φ [upN (length qs) sigma]
  = (quant_list_to_form qs φ)[sigma].
  Proof.
    induction qs as [|q qs IH] in sigma |-*.
    - now apply subst_ext.
    - cbn [quant_list_to_form]. cbn. f_equal. rewrite iter_switch. apply IH.
  Qed.

  Lemma quant_list_to_form_rename_free_up {b: falsity_flag} qs φ:
    quant_list_to_form qs φ [shift_quant (length qs) 1] = (quant_list_to_form qs φ)[↑].
  Proof.
    now erewrite <- (quant_list_to_form_rename_free).
  Qed.

  Lemma AllEquivAll :
    forall p q: D -> Prop, (forall d, (p d) <-> (q d)) -> ((forall d, (p d)) <-> forall d, (q d)).
  Proof. firstorder. Qed.

  Lemma ExEquivEx :
    forall p q: D -> Prop, (forall d, (p d) <-> (q d)) -> ((exists d, (p d)) <-> exists d, (q d)).
  Proof. firstorder. Qed.

  Lemma PNF_equiv_bin_op {b: falsity_flag} (DN: DN) ρ op φ1 φ2:
    ρ ⊨ ((convert_PNF (bin op φ1 φ2)) ↔ (bin op (convert_PNF φ1) (convert_PNF φ2))).
  Proof.
    unfold convert_PNF in *. cbn [conv_list conv_form].
    remember (conv_list φ1) as qs1. remember (conv_list φ2) as qs2.
    remember (conv_form φ1) as ψ1. remember (conv_form φ2) as ψ2.
    clear Heqqs1 Heqqs2 Heqψ1 φ1 Heqψ2 φ2.
    revert ρ ψ1 ψ2. induction qs1 as [| q1 qs1 IH1]; [induction qs2 as [|q2 qs2 IH2]|]; intros ρ φ1 φ2.
      + destruct op. all: cbn; split. all: repeat rewrite sat_comp. all: now setoid_rewrite (@sat_ext _ _ _ _ _ ρ ((shift 0 >> eval ρ))).
      + destruct op; destruct q2; cbn [app quant_list_to_form length].
        all: setoid_rewrite shift_quant_0.
        all: eapply equivTrans; [|apply PNF_andAll + apply PNF_andExists + apply (PNF_orAll DN) + apply PNF_orExists + apply PNF_implAll + apply (PNF_implExists (DN_to_IndependenceOfGeneralPremises DN))].
        all: assert (forall ρ a b, (ρ ⊨ (a ↔ b)) <-> (ρ ⊨ a <-> ρ ⊨ b)) as eqEquiv by firstorder.
        all: setoid_rewrite eqEquiv in IH2.
        all: cbn in *; apply AllEquivAll + apply ExEquivEx.
        all: intros d; rewrite <- IH2; apply quant_list_to_form_equiv.
        all: now setoid_rewrite shift_one_more; setoid_rewrite shift_quant_0.
      + destruct op; destruct q1; cbn [app quant_list_to_form].
        all: eapply equivTrans; [|apply PNF_allAnd + apply PNF_existsAnd + apply (PNF_allOr DN) + apply PNF_existsOr + apply (PNF_allImpl DN) + apply PNF_existsImpl].
        all: assert (forall ρ a b, (ρ ⊨ (a ↔ b)) <-> (ρ ⊨ a <-> ρ ⊨ b)) as eqEquiv by firstorder.
        all: setoid_rewrite eqEquiv in IH1.
        all: cbn in *; apply AllEquivAll + apply ExEquivEx.
        all: rewrite <- quant_list_to_form_rename_free_up; cbn in *.
        all: now intros d; rewrite <- IH1, shift_quant_1.
  Qed.

  Lemma PNF_equiv `{falsity_flag}:
    DN -> forall f ρ, sat ρ (f ↔ (convert_PNF f)).
  Proof.
    intros DN f ρ.
    induction f as [|b P v|b op ϕ1 IH1 ϕ2 IH2|b op ϕ IHϕ] in ρ |-*.
    - easy.
    - easy.
    - eapply equivTrans. 2: apply (PNF_equiv_bin_op DN).
      clear DN.
      destruct op; cbn in *.
      all: firstorder.
    - unfold convert_PNF in *. cbn.
      destruct op; firstorder.
  Qed.

End PrenexNormalForm.

(* PNF_equiv -> DN *)

Lemma PNF_equiv_DN : (forall (D : Type) (Σ_preds : preds_signature) (Σ_funcs : funcs_signature) (i : interp D) (ff : falsity_flag),
  forall (f : form) (ρ : env D), ρ ⊨ (f ↔ convert_PNF f)) -> DN.
Proof.
  intros H P nnP.
  specialize (H (option P) PA_preds_signature PA_funcs_signature).
  pose ({|
    i_func :=
      fun (_tmp : PA_funcs_signature) (_ : vec (option P) (ar_syms _tmp)) =>
      None;
    i_atom :=
      fun P0 : PA_preds_signature =>
      match P0 as p return (vec (option P) (ar_preds p) -> Prop) with
      | Eq =>
          fun v : vec (option P) (ar_preds Eq) =>
          Vector.hd v = Vector.hd (Vector.tl v)
      end
  |}) as i.
  specialize (H i falsity_on (¬(∀ ($0 == $1))) (fun _ => None)). cbn in H.
  destruct H as [[x H] _].
  - intros A. apply nnP. intros p. specialize (A (Some p)) as [=].
  - destruct x.
    + exact p.
    + contradiction.
Qed.
