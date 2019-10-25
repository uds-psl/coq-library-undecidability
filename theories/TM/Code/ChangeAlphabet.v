From Undecidability Require Import TM.Prelim TM.Code.CodeTM.
From Undecidability Require Import TM.Lifting.LiftAlphabet.


(** * Alphabet-lift for "programmed" Turing Machines *)

(** All "programmed" Turing machines are defined on an alphabet [Σ^+]. In this module, we instanciate the [LiftAlphabet] operator. Given a machine [M:TM_{Σ^+}] and a retraction [f: Σ ↪ Γ], we define a machine [⇑M : TM_{Γ^+}]. *)


Generalizable All Variables.

Section SurjectInject.
  Variable (sig tau : Type).
  Variable def : sig.
  Variable retr : Retract sig tau.

  Definition injectSymbols : list sig -> list tau := map Retr_f.
  Definition surjectSymbols : list tau -> list sig := map (surject Retr_g def).

  (* This can be easyly proven without induction. *)
  Lemma surject_inject (str : list sig) (str' : list tau) :
    injectSymbols str = str' ->
    str = surjectSymbols str'.
  Proof.
    intros <-. induction str as [ | s str IH ]; cbn.
    - reflexivity.
    - unfold surject. retract_adjoint. f_equal. auto.
  Qed.

  Lemma inject_surject (str : list tau) (str' : list sig) :
    (forall t, t el str -> exists s, Retr_g t = Some s) ->
    surjectSymbols str = str' ->
    str = injectSymbols str'.
  Proof.
    intros H <-. unfold injectSymbols, surjectSymbols. rewrite map_map. erewrite map_ext_in. symmetry. eapply map_id.
    intros t Ht. specialize (H _ Ht) as (s&Hs).
    erewrite retract_g_inv; eauto.
    unfold surject. rewrite Hs. reflexivity.
  Qed.

  Lemma surject_cons (str : list tau) (str2 : list sig) (s : sig) :
    surjectSymbols str = s :: str2 ->
    exists (t : tau) (str' : list tau),
      str = t :: str' /\
      surject Retr_g def t = s /\
      surjectSymbols str' = str2.
  Proof.
    destruct str as [ | t str ]; cbn in *; intros; inv H; eauto.
  Qed.

  Lemma surject_app (str : list tau) (str2 str3 : list sig) :
    surjectSymbols str = str2 ++ str3 ->
    exists (str' str'' : list tau),
      str = str' ++ str'' /\
      surjectSymbols str'  = str2 /\
      surjectSymbols str'' = str3.
  Proof.
    revert str str3. induction str2 as [ | s str2 IH]; intros str str3 H; cbn in *.
    - exists nil, str. cbn. auto.
    - pose proof surject_cons H as (t&str'&->&L1&L2). cbn in *. specialize (IH _ _ L2) as (Str&Str'&->&IH1&IH2).
      inv H. repeat eexists. instantiate (1 := t :: Str). reflexivity. cbn. reflexivity.
  Qed.

End SurjectInject.


Corollary map_length_eq : forall (A B C : Type) (f : A -> C) (g : B -> C) (l1 : list A) (l2 : list B), map f l1 = map g l2 -> |l1| = |l2|.
Proof.
  intros. erewrite <- map_length. symmetry. erewrite <- map_length. symmetry. rewrite H. reflexivity.
Qed.


Section MapCode.
  Variable sig tau : Type.
  Variable retr : Retract sig tau.

  Variable (sigX X : Type) (cX : codable sigX X) (I_x : Retract sigX sig) (I : Retract sig tau).

  Global Instance Retract_plus : Retract (boundary + sig) (boundary + tau) := Retract_sum _ _.
  Notation "'f''" := (@Retr_f (boundary+sig) (boundary+tau) Retract_plus).
  Notation "'g''" := (@Retr_g (boundary+sig) (boundary+tau) Retract_plus).

  Local Arguments Retr_f {X Y} (Retract).
  Local Arguments Retr_g {X Y} (Retract).

  Local Instance I_x' : Retract sigX tau := ComposeRetract _ _.


  (* Translation Functions *)
  Notation injectTape := (mapTape f').
  Notation surjectTape := (surjectTape g' (inl UNKNOWN)).

  (* Check injectTape : tape (sig^+) -> tape (tau^+) . *)
  (* Check surjectTape : tape (tau^+) -> tape (sig^+). *)

  (* The other direction does not hold *)
  Lemma surjectTape_injectTape t :
    surjectTape (injectTape t) = t.
  Proof.
    unfold surjectTape. unfold surject. simpl_tape.
    erewrite mapTape_ext. apply mapTape_id. intros a. retract_adjoint. reflexivity.
  Qed.

  Lemma contains_size_translate_sig (s : nat) (x : X) (t : tape (boundary+sig)) :
    t ≃(;s) x <-> (injectTape t) ≃(;s) x.
  Proof.
    split; intros (r1&HCode&Hs); subst; cbn in *; hnf.
    - repeat eexists. cbn. f_equal. rewrite map_app, !List.map_map. cbn. reflexivity.
      now simpl_list.
    - unfold injectTape in HCode.
      exists (surjectSymbols (inl UNKNOWN) _ r1).
      apply mapTape_inv_midtape in HCode as (ls'&m'&rs'&->&->&HCode1&HCode2).
      rewrite map_map in HCode2.
      destruct m'; cbn in *; inv HCode1.
      split. f_equal.
      + unfold surjectSymbols. rewrite map_map. rewrite <- map_id at 1. eapply List.map_ext.
        intros [ | ]; cbn. reflexivity. unfold surject. cbn. retract_adjoint. reflexivity.
      + symmetry. eapply map_injective with (f := retract_sum_f id (Retr_f _)); eauto.
        { intros. eapply retract_f_injective; eauto. }
        now rewrite map_app, !map_map.
      + unfold surjectSymbols. rewrite map_length in Hs. simpl_list. omega.
  Qed.

  Corollary contains_translate_sig (x : X) (t : tape (boundary+sig)) :
    t ≃ x <-> (injectTape t) ≃ x.
  Proof.
    split; intros.
    - eapply tape_contains_size_contains. apply contains_size_translate_sig.
      contains_ext.
    - eapply tape_contains_size_contains. apply contains_size_translate_sig. contains_ext.
  Qed.

  Lemma contains_size_translate_tau1 (x : X) (s : nat) (t : tape (boundary+tau)) :
    t ≃(;s) x -> surjectTape t ≃(;s) x.
  Proof.
    intros (ls&HCode&Hs). cbn in *. subst. cbn. rewrite !map_map.
    repeat econstructor.
    - f_equal. cbn. rewrite map_app, !map_map. f_equal.
      eapply List.map_ext. intros. unfold surject. cbn. unfold retr_comp_f. cbn. retract_adjoint. reflexivity.
    - now simpl_list.
  Qed.

  Corollary contains_translate_tau1 (x : X) (t : tape (boundary+tau)) :
    t ≃ x -> surjectTape t ≃ x.
  Proof.
    intros. eapply tape_contains_size_contains. apply contains_size_translate_tau1. contains_ext.
  Qed.
    

  Lemma surject_inject_inr (x : boundary) (str : list (boundary+tau)) (code : list sig) :
    surjectSymbols (inl x) Retract_plus str = map inr code ->
    exists str' : list tau, str = map inr str' /\ map (Retr_g I) str' = map Some code.
  Proof.
    revert x code. induction str as [ | s str' IH]; intros; cbn in *.
    - apply map_eq_nil' in H as ->. exists nil. cbn. tauto.
    - destruct code as [ | c code']; cbn in *; inv H.
      destruct s; cbn in *; inv H1.
      specialize (IH _ _ H2) as (str''&->&IH). rewrite <- IH.
      exists (t :: str''). cbn. split. auto. f_equal.
      unfold surject, retract_sum_g in H0. destruct (Retr_g I t) eqn:E; inv H0; auto.
  Qed.

  Lemma in_encode_retract (x : X) :
    forall t' : tau, t' el Encode_map cX _ x -> exists s' : sig, Retr_g I t' = Some s'.
  Proof. cbn. intros t' (?&<-&?) % in_map_iff. unfold retr_comp_f. cbn. retract_adjoint. eauto. Qed.

  Lemma contains_size_translate_tau2 (x : X) (s : nat) (t : tape (boundary+tau)) :
    surjectTape t ≃(;s) x ->
    t ≃(;s) x.
  Proof.
    intros (r1&HCode&Hs). cbn in *.
    eapply mapTape_inv_midtape in HCode as (ls'&m'&rs'&->&->&HCode1&HCode2).
    repeat econstructor; cbn in *. f_equal.
    - unfold surject in HCode1. destruct m'; cbn in *. cbv [id] in *. now inv HCode1.
      destruct (Retr_g I t); inv HCode1.
    - symmetry in HCode2.
      change (surjectSymbols (inl UNKNOWN) Retract_plus rs' = map inr (Encode_map cX _ x) ++ [inl STOP]) in HCode2.
      eapply surject_app in HCode2 as (str1&str2&->&L1&L2).
      eapply inject_surject in L1 as ->; eauto.
      eapply inject_surject in L2 as ->; eauto.
      + f_equal. unfold injectSymbols. cbn. rewrite !map_map. eapply List.map_ext. intros. cbn. reflexivity.
      + unfold surjectSymbols in L2. eapply map_eq_cons in L2 as (t & ? & -> & ? & -> % map_eq_nil').
        unfold surject in H. destruct t; cbn in *; swap 1 2. destruct (Retr_g I t); inv H. inv H.
        intros [ | ]; intros [ | ]; try congruence; auto. inv H. eexists. cbn. reflexivity.
      + intros [ | ]; intros He; cbn; eauto.
        destruct (Retr_g I t) eqn:E1; cbn; eauto. exfalso.
        pose proof surject_inject_inr L1 as (str1'&->&L3).
        apply in_map_iff in He as (?&HETmp&HE); inv HETmp.
        enough (t el (Encode_map cX _ x)) as L4.
        {
          pose proof in_encode_retract L4 as (?&?). congruence.
        }
        cbn in *.
        assert (None el map (Retr_g I) str1') as L5.
        {
          rewrite <- E1. eapply in_map_iff; eauto.
        }
        rewrite L3 in L5. apply in_map_iff in L5 as (?&?&?). congruence.
    - now rewrite map_length in Hs.
  Qed.

  Corollary contains_translate_tau2 (x : X) (t : tape (boundary+tau)) :
    surjectTape t ≃ x ->
    t ≃ x.
  Proof.
    intros. eapply tape_contains_size_contains. apply contains_size_translate_tau2. contains_ext.
  Qed.

  Corollary contains_size_translate_tau (x : X) (s : nat) (t : tape (boundary+tau)) :
    surjectTape t ≃(;s) x <-> t ≃(;s) x.
  Proof. split; auto using contains_size_translate_tau1, contains_size_translate_tau2. Qed.

  Corollary contains_translate_tau (x : X) (t : tape (boundary+tau)) :
    surjectTape t ≃ x <-> t ≃ x.
  Proof. split; auto using contains_translate_tau1, contains_translate_tau2. Qed.

  Corollary contains_size_translate_eq (t1 t2 : tape (boundary+tau)) (s : nat) (x : X) :
    surjectTape t1 = surjectTape t2 ->
    t1 ≃(;s) x -> t2 ≃(;s) x.
  Proof.
    intros HEq HEnc.
    eapply contains_size_translate_tau2; auto.
    rewrite <- HEq. now eapply contains_size_translate_tau1 in HEnc.
  Qed.

  Corollary contains_translate_eq (t1 t2 : tape (boundary+tau)) (x : X) :
    surjectTape t1 = surjectTape t2 ->
    t1 ≃ x -> t2 ≃ x.
  Proof.
    intros. eapply tape_contains_size_contains. eapply contains_size_translate_eq; eauto.
  Qed.

  Lemma surjectTape_isVoid_size (t : tape (boundary+tau)) (s : nat) :
    isVoid_size t s -> isVoid_size (surjectTape t) s.
  Proof. unfold surjectTape. apply mapTape_isVoid_size. Qed.

  Lemma surjectTape_isVoid'_size (t : tape (boundary+tau)) (s : nat) :
    isVoid_size (surjectTape t) s -> isVoid_size t s.
  Proof. unfold surjectTape. apply mapTape_isVoid_size. Qed.

  Lemma surjectTape_isVoid (t : tape (boundary+tau)) :
    isVoid t -> isVoid (surjectTape t).
  Proof. unfold surjectTape. apply mapTape_isVoid. Qed.

  Lemma surjectTape_isVoid' (t : tape (boundary+tau)) :
    isVoid (surjectTape t) -> isVoid t.
  Proof. unfold surjectTape. apply mapTape_isVoid. Qed.

End MapCode.

Hint Unfold surjectTape surjectTapes injectTape : tape.

(** This makes sure that we can apply the above lemmas ([contains_translate_sig], [contains_translate_tau1], [contains_translate_tau2]), even after [cbn] *)
Arguments Retract_plus : simpl never.
Arguments injectTape : simpl never.
Arguments surjectTape : simpl never.


(** ** Definition of the lifted machine *)

Section ChangeAlphabet.
  Variable (sig tau : finType).
  Variable (n : nat) (F : finType).
  Variable pM : pTM sig^+ F n.
  Variable (retr : Retract sig tau).

  Definition ChangeAlphabet : pTM tau^+ F n :=
    LiftAlphabet pM (Retract_plus retr) (inl UNKNOWN).

End ChangeAlphabet.


(** This tactic removes [surjectTape] in hypothesises and in the goal *)
Ltac simpl_surject_step :=
  lazymatch goal with
  (* encodings *)
  | [ |- surjectTape _ _ ?t ≃ _ ] => apply contains_translate_tau1
  | [ H : surjectTape _ _ ?t ≃ _ |- _ ] => apply contains_translate_tau2 in H
  | [ |- surjectTape _ _ ?t ≃(;?n) _ ] => apply contains_size_translate_tau1
  | [ H : surjectTape _ _ ?t ≃(;?n) _ |- _ ] => apply contains_size_translate_tau2 in H
  (* [isVoid] and [isVoid_size] *)
  | [ |- isVoid (surjectTape _ _ ?t) ] => apply surjectTape_isVoid
  | [ H : isVoid (surjectTape _ _ ?t) |- _ ] => apply surjectTape_isVoid' in H
  | [ |- isVoid_size (surjectTape _ _ ?t) ?n ] => apply surjectTape_isVoid_size
  | [ H : isVoid_size (surjectTape _ _ ?t) ?n |- _ ] => apply surjectTape_isVoid'_size in H
  end.

Ltac simpl_surject := repeat simpl_surject_step.


(** ** Tactic Support *)

Ltac smpl_TM_ChangeAlphabet :=
  lazymatch goal with
  | [ |- ChangeAlphabet ?pM ?retr ⊨ _ ] => apply LiftAlphabet_Realise
  | [ |- ChangeAlphabet ?pM ?retr ⊨c(_) _ ] => apply LiftAlphabet_RealiseIn
  | [ |- projT1 (ChangeAlphabet ?pM ?retr) ↓ _ ] => apply LiftAlphabet_TerminatesIn
  end.


Smpl Add smpl_TM_ChangeAlphabet : TM_Correct.
