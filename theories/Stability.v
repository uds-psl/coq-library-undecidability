From Undecidability.FOLC Require Import ND.
From Undecidability.FOLC Require Import GenTarski.

(* ** Constructive Analysis *)

Definition stable P := ~ ~ P -> P.

Lemma stable_equiv P Q :
  P <-> Q -> stable P -> stable Q.
Proof.
  firstorder.
Qed.

Definition stab_class := forall Sigma, @theory Sigma -> Prop.
Definition map_closed (S : stab_class) {Sig Sig'} (f : @form Sig -> @form Sig') := forall T, S Sig T -> S Sig' (tmap f T).

Definition ST (S : stab_class) := forall Sigma T phi, S Sigma T -> stable (T ⊩CE phi).

Section PropT.
  Definition dummy_sig : Signature := {| Funcs := False; Preds := False; pred_ar := @except nat ; fun_ar := @except nat |}.

  Definition prop_T (P : Prop) := fun phi : @form dummy_sig => phi = ⊥ /\ P.

  Lemma prop_T_correct P :
    prop_T P ⊩CE ⊥ <-> P.
  Proof.
    split.
    - intros ([ | x] & HA1 & HA2). 1: contradiction (Consistency HA2).
      destruct (HA1 x (or_introl eq_refl)). firstorder.
    - exists [⊥]; split. 2: ctx. now intros ? [<- | []].
  Qed.

  Global Instance False_enumT : enumT False.
  Proof.
    exists (fun _ => []). 1: auto. intros [].
  Qed.
End PropT.

Section StabilityClasses.
  (* **** Double Negation Elimination *)

  Section DN.
    Definition DN := forall P, stable P.

    Definition any_T : stab_class := fun _ _ => True.
    Definition ST__a := ST any_T.

    Lemma any_T_map_closed {Sig Sig' : Signature} (f : @form Sig -> @form Sig') :
      map_closed any_T f.
    Proof.
      firstorder.
    Qed.

    Lemma dn_to_sta :
      DN -> ST__a.
    Proof.
      intros dn Sig T phi _. apply dn.
    Qed.

    Lemma sta_to_dn :
      ST__a -> DN.
    Proof.
      intros sta P. eapply stable_equiv. 1: apply (prop_T_correct P). now apply sta.
    Qed.
  End DN.

  (* **** Synthetic Markov's Principle *)

  Section SyntMP.
    Definition tsat (f : nat -> bool) := exists n, f n = true.
    Definition MP := forall f : nat -> bool, stable (tsat f).

    Definition enum_T : stab_class := fun _ T => exists (HdF : eq_dec Funcs) (HdP : eq_dec Preds)
                                                (HeF : enumT Funcs) (HeP : enumT Preds) L, enum T L.
    Definition ST__e := ST enum_T.

    Lemma enum_T_map_closed_closing {Sig : Signature} :
      @map_closed enum_T Sig (sig_ext Sig) (fun phi => (sig_lift phi)[ext_c]).
    Proof.
      intros T (? & ? & ? & ? & L & He). exists (dec_sig_ext_Funcs _), (dec_sig_ext_Preds _).
      exists (enumT_sig_ext_Funcs _), (enumT_sig_ext_Preds _), (L >> map (fun phi => (sig_lift phi)[ext_c])).
      now apply enum_tmap.
    Qed.

    Lemma enum_T_map_closed_homo {Sig : Signature} (f : @form Sig -> @form Sig) :
      map_closed enum_T f.
    Proof.
      intros T (HdF' & HdP' & HeF' & HeP' & L & He). exists HdF', HdP', HeF', HeP', (L >> map f).
      now apply enum_tmap.
    Qed.
    
    Section MPEnum.
      Hypothesis mp : MP.
      Variable (X : Type) (L : nat -> list X) (P : X -> Prop).
      Hypothesis (HL : enum P L) (HX : eq_dec X).

      Lemma enumeration_semi_decidable x :
        exists (f : nat -> bool), P x <-> tsat f.
      Proof.
        destruct HL as [_ H]. exists (fun n => if list_in_dec x (L n) HX then true else false).
        split.
        - intros [m ?] % H. exists m. now destruct (list_in_dec x (L m) HX).
        - intros [m Hm]. destruct (list_in_dec x (L m) HX) in Hm. 2: discriminate. firstorder.
      Qed.

      Lemma enumeration_stability x :
        stable (P x).
      Proof.
        intros Hn. destruct (enumeration_semi_decidable x) as [f Hf].
        apply Hf. apply mp. intros Hf'. apply Hn. intros [m Hm] % Hf. apply Hf'. now exists m.
      Qed.
    End MPEnum.

    Lemma mp_to_ste :
      MP -> ST__e.
    Proof.
      intros mp Sig T phi (? & ? & ? & ? & L & He).  apply (enumeration_stability mp (enum_tprv He) (dec_form _ _)).
    Qed.

    Fixpoint L_tsat_T (f : nat -> bool) (n : nat) : list (@form dummy_sig) :=
      match n with
      | 0 => []
      | S n => L_tsat_T f n ++ if f n then [⊥] else []
      end.

    Lemma enum_tsat_T (f : nat -> bool) :
      enum (prop_T (tsat f)) (L_tsat_T f).
    Proof.
      split. 1: eauto. split.
      - intros [-> [n H]]. exists (S n). cbn. rewrite H. now in_app 2.
      - intros [n]. induction n in x, H |-*; cbn in *. 1: contradiction. inv_collect.
        destruct (f n) eqn:Hf.
        + destruct H as [<- | []]. firstorder.
        + contradiction.
    Qed.

    Lemma ste_to_mp :
      ST__e -> MP.
    Proof.
      intros ste f. eapply stable_equiv. 1: apply prop_T_correct.
      apply ste. exists _, _, _, _, (L_tsat_T f). apply (enum_tsat_T f).
    Qed.
  End SyntMP.

  (* **** Object Markov's Principle *)

  Section ObjMP.
    Definition fin_T : stab_class := fun Sig T => exists A, forall phi, phi ∈ T <-> phi el A.
    Definition ST__f := ST fin_T.

    Lemma fin_T_map_closed {Sig Sig'} (f : @form Sig -> @form Sig') :
      map_closed fin_T f.
    Proof.
      intros T [A HA]. exists (map f A). intros phi. split.
      - intros (psi & Hpsi1 % HA & <-). now apply in_map.
      - intros (psi & <- & Hpsi) % in_map_iff. firstorder.
    Qed.

    Section ConT.
      Context {Sigma : Signature}.
      Context {p : peirce} {b : bottom}.

      Definition con_T A : theory := fun phi => phi el A.

      Lemma con_T_correct A phi :
         con_T A ⊩ phi <-> A ⊢ phi.
      Proof.
        firstorder. apply (Weak H0). firstorder.
      Qed.

      Lemma fin_T_con_T A :
        fin_T (con_T A).
      Proof.
        firstorder.
      Qed.
    End ConT.

    Lemma fin_T_to_context {Sig : Signature} T phi :
      fin_T T -> exists A, A ⊢CE phi <-> T ⊩CE phi.
    Proof.
      intros [A HA]. exists A. split.
      - intros; exists A; firstorder.
      - intros (B & HB1 & HB2). apply (Weak HB2). firstorder.
    Qed.

    Lemma stf_to_st_context :
      ST__f <-> (forall Sigma A (phi : @form Sigma), stable (A ⊢CE phi)).
    Proof.
      split.
      - intros stf Sig A phi. eapply stable_equiv. 1: apply con_T_correct.
        apply stf. apply fin_T_con_T.
      - intros stc Sig T phi HT. destruct (fin_T_to_context phi HT) as [A HA].
        eapply stable_equiv. apply HA. apply stc.
    Qed.
  End ObjMP.
End StabilityClasses.
