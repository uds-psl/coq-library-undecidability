Set Default Goal Selector "!".

Require Import
  Undecidability.StackMachines.BSM Undecidability.StackMachines.Util.BSM_computable
  Undecidability.TM.TM Undecidability.TM.Util.TM_facts Undecidability.TM.Util.TM_computable.
From Undecidability.TM Require Import TM Arbitrary_to_Binary mTM_to_TM HaltTM_1_to_HaltKOSBTM HaltKOSBTM_to_HaltBSM.
From Undecidability.Shared.Libs.DLW Require Import vec pos sss subcode.
From Undecidability Require Import bsm_utils bsm_defs.
Require Import Undecidability.TM.Code.Code.
From Undecidability.Shared.Libs.PSL Require FinTypes.
From Undecidability.TM Require Import Single.EncodeTapes.

Notation "v @[ t ]" := (Vector.nth v t) (at level 50).

Lemma skipn_app' (X : Type) (xs ys : list X) (n : nat) :
  n = (| xs |) -> skipn n (xs ++ ys) = ys.
Proof. intros ->. now rewrite List.skipn_app, skipn_all, Nat.sub_diag. Qed.

Lemma vec_app_spec {X n m} (v : Vector.t X n) (w : Vector.t X m) :
  vec_app v w = Vector.append v w.
Proof.
  induction v.
  - cbn. eapply vec_pos_ext. intros. now rewrite vec_pos_set.
  - rewrite vec_app_cons. cbn. congruence.
Qed.

Lemma cast_eq_refl {X n} (v : Vector.t X n) E : Vector.cast v E = v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma vec_list_inj {X n} (v w : Vector.t X n) :
  vec_list v = vec_list w -> v = w.
Proof.
  induction v in w |- *.
  - pattern w. revert w. eapply Vector.case0. reflexivity.
  - eapply (Vector.caseS' w). clear w. intros y w. cbn.
    intros [= ->]. f_equal. eauto.
Qed.

Lemma vector_inv_back {X n} (v : Vector.t X (S n)) E :
  { '(x, v') : X * Vector.t X n | v = Vector.cast (Vector.append v' (x ## vec_nil)) E }.
Proof.
  destruct E. 
  destruct (Vector.splitat n v) eqn:E.
  eexists (vec_head t0, t).
  erewrite <- Vector.append_splitat. 1: now rewrite cast_eq_refl.
  rewrite E. f_equal. eapply (Vector.caseS' t0). cbn.
  intros h. eapply Vector.case0. reflexivity.
Qed.

Lemma nth_error_vec_list {X n} (v : Vector.t X n) m (H : m < n) x :
  nth_error (vec_list v) m = Some x ->
  vec_pos v (Fin.of_nat_lt H) = x.
Proof.
  induction v in m , H |- *; cbn.
  - lia.
  - destruct m; cbn.
    + congruence.
    + eapply IHv.
Qed.

Lemma vec_list_cast {X n} (v :Vector.t X n) m (E : n = m) :
 vec_list (Vector.cast v E) = vec_list v.
Proof.
  destruct E. now rewrite cast_eq_refl.
Qed.

Lemma vec_list_vec_app {X n m} (v : Vector.t X n) (w : Vector.t X m) :
  vec_list (vec_app v w) = vec_list v ++ vec_list w.
Proof.
  rewrite ! vec_app_spec.
  induction v in w |- *.
  - cbn. reflexivity.
  - cbn. f_equal. eauto.
Qed.

Lemma vec_list_const {X x n} : vec_list (@Vector.const X x n) = List.repeat x n.
Proof. induction n; cbn; congruence. Qed.

Fixpoint update {X} (n : nat) (l : list X) y :=
  match l, n with
  | nil, _ => nil
  | x :: l, 0 => y :: l
  | x :: l, S n => x :: update n l y
  end.

Lemma update_app_right {X} (x : X) l1 l2 i : 
  i >= length l1 ->
  update i (l1 ++ l2) x = l1 ++ update (i - length l1) l2 x.
Proof.
  induction l1 in i |- *; cbn.
  - now rewrite Nat.sub_0_r.
  - intros Hi. destruct i. 1: lia.
    cbn. rewrite IHl1. 1: reflexivity. lia.
Qed.

Lemma update_app_left {X} (x : X) l1 l2 i : 
  i < length l1 ->
  update i (l1 ++ l2) x = update i l1 x ++ l2.
Proof.
  induction l1 in i |- *; cbn.
  - lia. 
  - intros Hi. destruct i; cbn.
    + reflexivity.
    + rewrite IHl1. 1: reflexivity. lia.
Qed.

Lemma vec_list_vec_change {X n} (v : Vector.t X n) (x : X) (p : pos n) :
  vec_list (vec_change v p x) = update (proj1_sig (Fin.to_nat p)) (vec_list v) x.
Proof.
  induction v; cbn.
  - inversion p.
  - eapply (Fin.caseS' p); cbn.
    + cbn. reflexivity. 
    + intros. specialize (IHv p0). destruct (Fin.to_nat p0) eqn:E. cbn in *. now f_equal.
Qed.

Definition complete_encode (Σ : finType) n (t : Vector.t (tape Σ) n) :=
  (conv_tape [| encode_tape' (Vector.nth (mTM_to_TM.enc_tape [] t) Fin0) |]).

Lemma KOSBTM_complete_simulation n Σ (M : TM Σ n) :
  {M' : KOSBTM.KOSBTM |
        (forall q t t', TM.eval M (TM.start M) t q t' -> exists q', KOSBTM.eval M' Fin.F1 (complete_encode t) q' (complete_encode t')) /\
        (forall t, (exists q' t', KOSBTM.eval M' Fin.F1 (complete_encode t) q' t') -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (TM_sTM_simulation M) as (M1 & Hf1 & Hb1).
  destruct (binary_simulation M1) as (M2 & Hf2 & Hb2).
  destruct (KOSBTM_simulation M2) as (M3 & Hf3 & Hb3).
  exists M3. split.
  - intros q t t' [q1 [q2 [q3 H] % Hf3] % Hf2] % Hf1. eexists. eapply H.
  - intros t H % Hb3 % Hb2 % Hb1. exact H.
Qed.

Definition bsm_addstracks' n m (P : bsm_instr n) : (bsm_instr (m + n)) :=
  (fun x => match x with
  | bsm_pop x c1 c2 => bsm_pop (pos_right m x) c1 c2
  | bsm_push x b => bsm_push (pos_right m x) b end) P.

Definition bsm_addstacks n m (P : list (bsm_instr n)) : list (bsm_instr (m + n)):=
  map (@bsm_addstracks' n m) P.

Lemma vec_pos_spec {k} {X} (p : pos k) (v : Vector.t X k) : vec_pos v p = Vector.nth v p.
Proof.
  induction v in p |- *.
  - inversion p.
  - eapply (Fin.caseS' p).
    + reflexivity.
    + intros. cbn. eauto.
Qed.

Lemma vec_change_app_right {X} (n m : nat) v1 v2 p x:
  vec_change (@vec_app X n m v1 v2) (pos_right n p) x = vec_app v1 (vec_change v2 p x).
Proof.
  induction v1.
  - rewrite !vec_app_nil. reflexivity.
  - rewrite !vec_app_cons. cbn. now rewrite IHv1.
Qed.


Lemma pos_right_left {n m} p q :
@pos_left n m p <> @pos_right n m q.
Proof.
induction n; cbn.
- inversion p.
- eapply (Fin.caseS' p).
  + cbn. congruence.
  + cbn. intros ? ? % pos_nxt_inj. firstorder.
Qed.

Lemma pos_left_right {n m} p q :
@pos_right n m q <> @pos_left n m p.
Proof.
induction n; cbn.
- inversion p.
- eapply (Fin.caseS' p).
  + cbn. congruence.
  + cbn. intros ? ? % pos_nxt_inj. firstorder.
Qed.
Local Hint Immediate pos_left_right pos_right_left : core.

Lemma vec_change_app_left {X} (n m : nat) v1 v2 p x:
  vec_change (@vec_app X n m v1 v2) (pos_left m p) x = vec_app (vec_change v1 p x) v2.
Proof.
  eapply vec_pos_ext. eapply pos_left_right_rect.
  - intros. rewrite !vec_pos_app_left.
    destruct (pos_eq_dec p p0).
    + subst. rewrite vec_change_eq. 2: reflexivity. now rewrite vec_change_eq.
    + rewrite vec_change_neq. 2: intros ? % pos_left_inj; congruence.
      rewrite vec_pos_app_left. rewrite vec_change_neq; auto.
  - intros p0. rewrite !vec_pos_app_right. rewrite vec_change_neq; auto. now rewrite vec_pos_app_right.
Qed.

Lemma vec_app_inj {X} (n m : nat) v1 v2 v2' :
  @vec_app X n m v1 v2 = vec_app v1 v2' -> v2 = v2'.
Proof.
  induction v1.
  - now rewrite !vec_app_nil.
  - rewrite !vec_app_cons. intros. eapply IHv1.
    now eapply (f_equal (@vec_tail _ _)) in H.
Qed.

Lemma BSM_addstacks_step n m (P : bsm_instr n) j v o v' v'' :
   (bsm_sss P (j, v) (o, v') <-> bsm_sss (@bsm_addstracks' n m P) (j, vec_app v'' v) (o, vec_app v'' v')).
Proof.
  destruct P; cbn; intros; split; inversion 1; subst.
  - econstructor. now rewrite vec_pos_app_right.
  - rewrite <- vec_change_app_right. econstructor 2.
    now rewrite !vec_pos_app_right.
  - rewrite <- vec_change_app_right. econstructor 3.
    now rewrite !vec_pos_app_right.
  - rewrite vec_pos_app_right in H1.
    match goal with |- bsm_sss _ _ ?st => evar (ev : bsm_state n); enough (st = ev) as ->; subst ev end.
    1: econstructor 1.  1: eassumption. f_equal. now eapply vec_app_inj in H7.
  - rewrite vec_pos_app_right in H1. rewrite vec_change_app_right in H7.
    match goal with |- bsm_sss _ _ ?st => evar (ev : bsm_state n); enough (st = ev) as ->; subst ev end.
    1: econstructor 2.  1: eassumption. f_equal.  now eapply vec_app_inj in H7.
  - rewrite vec_pos_app_right in H1. rewrite vec_change_app_right in H7.
    match goal with |- bsm_sss _ _ ?st => evar (ev : bsm_state n); enough (st = ev) as ->; subst ev end.
    1: econstructor 3.  1: eassumption. f_equal.  now eapply vec_app_inj in H7.
  - match goal with |- bsm_sss _ _ ?st => evar (ev : bsm_state (m + n)); enough (st = ev) as ->; subst ev end.
  1: econstructor 4. f_equal. now rewrite vec_change_app_right, vec_pos_app_right.
  - match goal with |- bsm_sss _ _ ?st => let X := type of st in evar (ev : X); enough (st = ev) as ->; subst ev end.
  1: econstructor 4. f_equal. rewrite vec_change_app_right, vec_pos_app_right in H6. now eapply vec_app_inj in H6 as ->.
Qed.

Lemma BSM_addstacks_step_bwd n m (P : bsm_instr n) j v out v'' :
   bsm_sss (@bsm_addstracks' n m P) (j, vec_app v'' v) out -> exists o v', out = (o, vec_app v'' v') /\ bsm_sss P (j, v) (o, v').
Proof.
  destruct P; cbn; inversion 1; subst.
  - repeat eexists. econstructor. now rewrite vec_pos_app_right in H6.
  - repeat eexists.  1: rewrite vec_change_app_right.  1: reflexivity.
    rewrite vec_pos_app_right in H6.
    now econstructor 2.
  - repeat eexists.  1: rewrite vec_change_app_right.  1: reflexivity.
    rewrite vec_pos_app_right in H6.
    now econstructor 3.
  - repeat eexists.  1: rewrite vec_change_app_right.  1: reflexivity.
    rewrite vec_pos_app_right. econstructor 4.
Qed.

Lemma BSM_addstacks_step' n i (P : list (bsm_instr n)) m j v o v' v'' :
  sss_step (bsm_sss (n := n)) (i, P) (j, v) (o, v') -> sss_step (bsm_sss (n := m + n)) (i, (@bsm_addstacks n m P)) (j, vec_app v'' v) (o, vec_app v'' v').
Proof.
  intros (? & ? & ? & ? & ? & ? & ? & ?). inv H. inv H0.
  unfold bsm_addstacks. rewrite map_app. cbn.
  eexists. eexists. eexists. eexists. eexists. split.  1: reflexivity. split.  1: rewrite map_length.  1: reflexivity.
  now rewrite <- BSM_addstacks_step.
Qed.

Lemma skipn_map n {X Y} (f : X -> Y) l :
 skipn n (map f l) = map f (skipn n l).
Proof.
  induction l in n |- *; destruct n; cbn; congruence.
Qed.

Lemma BSM_addstacks_step_bwd' n i (P : list (bsm_instr n)) m j v v'' out :
  sss_step (bsm_sss (n := m + n)) (i, (@bsm_addstacks n m P)) (j, vec_app v'' v) out -> exists o v', out = (o, vec_app v'' v') /\ sss_step (bsm_sss (n := n)) (i, P) (j, v) (o, v').
Proof.
  intros (? & ? & ? & ? & ? & ? & ? & ?). inv H. inv H0.
  assert (nth_error (bsm_addstacks m P) (length x0) = Some x1).  1: rewrite H4.  1: rewrite nth_error_app2. 2:lia.  1: rewrite Nat.sub_diag.  1: reflexivity.
  unfold bsm_addstacks in H.
  destruct (nth_error_Some P (|x0|)) as [_ HH].
  destruct (nth_error P (|x0|)) as [d | ] eqn:E. 2:{ exfalso. eapply HH; try reflexivity. erewrite <- (map_length _ P). unfold bsm_addstacks in H4. rewrite H4.
  rewrite app_length. cbn. lia. }
  pose proof (E' := E).
  eapply map_nth_error in E. unfold bsm_addstacks in H4. rewrite H4 in E.
  rewrite nth_error_app2 in E. 2:lia. rewrite Nat.sub_diag in E. cbn in E. inv E.
  eapply BSM_addstacks_step_bwd in H1 as (? & ? & ? & ?). subst.
  repeat eexists; eauto.
  1: f_equal.  1: instantiate (2 := firstn (length x0) P).
  1: instantiate (1 := skipn (1 + length x0) P).
  2:{ f_equal. rewrite firstn_length. enough (|x0| < |P|).  1: lia.
      eapply nth_error_Some. now rewrite E'. }
  rewrite <- (firstn_skipn (length x0) P) at 1.
  f_equal.
  clear - H4. induction x0 in P, H4 |- *.
  - cbn in *. destruct P; inv H4. destruct b, d; inv H0; eapply pos_right_inj in H1; subst; reflexivity.
  - destruct P; cbn in *; inv H4. rewrite IHx0.  1: f_equal. eauto.
Qed.

Lemma BSM_addstacks' n i (P : list (bsm_instr n)) m k j v o v' v'' :
  sss_steps (bsm_sss (n := n)) (i, P) k (j, v) (o, v') -> sss_steps (bsm_sss (n := m + n)) (i, (@bsm_addstacks n m P)) k (j, vec_app v'' v) (o, vec_app v'' v').
Proof.
  induction k in j, v, o, v' |- *; inversion 1; subst.
  - econstructor.
  - destruct st2. econstructor.  1: eapply BSM_addstacks_step'.  1: exact H1. eapply IHk, H2.
Qed.

Lemma BSM_addstacks_bwd' n i (P : list (bsm_instr n)) m k j v v'' out :
  sss_steps (bsm_sss (n := m + n)) (i, (@bsm_addstacks n m P)) k (j, vec_app v'' v) out -> exists o v', out = (o, vec_app v'' v') /\ sss_steps (bsm_sss (n := n)) (i, P) k (j, v) (o, v').
Proof.
  induction k in j, v, out |- *; inversion 1; subst.
  - repeat econstructor.
  - eapply BSM_addstacks_step_bwd' in H1 as (? & ? & ? & ?). subst.
    eapply IHk in H2 as (? & ? & ? & ?). subst.
    repeat eexists. econstructor.  1: eauto. eauto.
Qed.

Lemma BSM_addstacks n i (P : list (bsm_instr n)) m :
   {P' | length P = length P' /\ (forall j v o v', BSM.eval n (i, P) (j, v) (o, v') -> forall v'', BSM.eval (m + n) (i, P') (j, Vector.append v'' v) (o, Vector.append v'' v'))
          /\ forall v v'' j out, BSM.eval (m + n) (i, P') (j, Vector.append v'' v) out -> exists out, BSM.eval n (i, P) (j, v) out}.
Proof.
  exists (bsm_addstacks m P). split. { unfold bsm_addstacks. now rewrite map_length. }
  setoid_rewrite eval_iff.
  split.
  - intros j v o v' [[steps H1] H2] v''. split. 2:{ cbn. unfold bsm_addstacks. rewrite map_length. cbn in H2. lia. }
    exists steps. rewrite <- !vec_app_spec. now eapply BSM_addstacks'.
  - intros v v'' j [o1 o2] H. eapply eval_iff in H as [[steps H1] H2].
    rewrite <- vec_app_spec in H1.
    eapply BSM_addstacks_bwd' in H1 as (? & ? & ? & ?). inv H.
    eexists (_, _). eapply eval_iff. split.  1: eexists.  1: eapply H0.
    cbn in *. unfold bsm_addstacks in H2. rewrite map_length in H2. lia.
Qed.

Definition encode_bsm (Σ : finType) n (t : Vector.t (tape Σ) n) :=
  enc_tape (complete_encode t).
Arguments encode_bsm {_ _} _, _ {_} _.

Lemma encode_bsm_nil (Σ : finType) n   :
  { '(str2, n') | forall (t : Vector.t (tape Σ) n), (encode_bsm Σ (niltape ::: t))@[Fin2] =  str2 ++ (skipn n' ((encode_bsm Σ t)@[Fin2]))}.
Proof.
  eexists (_, _). cbn. intros t.
  unfold complete_encode, conv_tape.
    etransitivity.
    1: destruct destruct_vector_cons as (? & ? & E). 1: cbn - [skipn].
    1: apply Vector.cons_inj in E; inv E.
    1: reflexivity.
    symmetry. etransitivity.
    1: destruct destruct_vector_cons as (? & ? & E).  1: cbn - [skipn].
    1: apply Vector.cons_inj in E; inv E.
    1: reflexivity.
    1: cbn - [skipn].
    rewrite skipn_app'. 2: now rewrite length_encode_sym.
    instantiate (1 := encode_sym _ ++ true :: false :: encode_sym _ ++ true :: false :: encode_sym _).
    rewrite <- app_assoc. cbn. now rewrite <- app_assoc.
Qed.

Definition strpush_common_short (Σ : finType) (s b : Σ) :=
encode_sym
  (projT1
     (projT2
        (FinTypes.finite_n
           (finType_CS (boundary + sigList (EncodeTapes.sigTape Σ)))))
     (inl START)) ++
true
:: false
   :: encode_sym
        (projT1
           (projT2
              (FinTypes.finite_n
                 (finType_CS (boundary + sigList (EncodeTapes.sigTape Σ)))))
           (inr sigList_cons)) ++
      true
      :: false
         :: encode_sym
              (projT1
                 (projT2
                    (FinTypes.finite_n
                       (finType_CS
                          (boundary + sigList (EncodeTapes.sigTape Σ)))))
                 (inr (sigList_X (EncodeTapes.LeftBlank false)))) ++
            true
            :: false
               :: encode_sym
                    (projT1
                       (projT2
                          (FinTypes.finite_n
                             (finType_CS
                                (boundary + sigList (EncodeTapes.sigTape Σ)))))
                       (inr (sigList_X (EncodeTapes.MarkedSymbol b)))).

Definition strpush_common (Σ : finType) (s b : Σ) :=
strpush_common_short s b ++
                  true
                  :: false :: nil.

Definition strpush_zero (Σ : finType) (s b : Σ) :=
  strpush_common s b ++
                      encode_sym
                          (projT1
                             (projT2
                                (FinTypes.finite_n
                                   (finType_CS
                                      (boundary +
                                       sigList (EncodeTapes.sigTape Σ)))))
                             (inr (sigList_X (EncodeTapes.RightBlank false)))).

Lemma encode_bsm_at0 (Σ : finType) n (t : Vector.t (tape Σ) n) :
   (encode_bsm Σ t) @[Fin0] = [].
Proof.
  unfold encode_bsm, enc_tape, complete_encode, conv_tape.
  destruct destruct_vector_cons as (? & ? & E).
  1: cbn; apply Vector.cons_inj in E; inv E.
  reflexivity.
Qed.

Lemma encode_bsm_at1 (Σ : finType) n :
   forall (t : Vector.t (tape Σ) n), (encode_bsm Σ t) @[Fin1] = [false].
Proof.
  intros t.
  unfold encode_bsm, enc_tape, complete_encode, conv_tape.
  destruct destruct_vector_cons as (? & ? & E).
  1: cbn; apply Vector.cons_inj in E; inv E.
  reflexivity.
Qed.

Lemma encode_bsm_at3 (Σ : finType) n (t : Vector.t (tape Σ) n) :
   (encode_bsm Σ t) @[Fin3] = [].
Proof.
  unfold encode_bsm, enc_tape, complete_encode, conv_tape.
  destruct destruct_vector_cons as (? & ? & E).
  1: cbn; apply Vector.cons_inj in E; inv E.
  reflexivity.
Qed.

Axiom FF : False.

Lemma encode_bsm_zero (Σ : finType) s b :
  { n' | forall n(t : Vector.t (tape Σ) n), (encode_bsm Σ (encNatTM s b 0 ::: t)) @[Fin2] = strpush_zero s b ++ (skipn n' ((encode_bsm Σ t)@[Fin2]))}.
Proof.
  eexists _. intros t.
  unfold encode_bsm at 1.
  unfold enc_tape at 1.
  cbn.
  unfold complete_encode, conv_tape.
  etransitivity.
  1: destruct destruct_vector_cons as (? & ? & E). 1: cbn [projT1]. 1: apply Vector.cons_inj in E; inv E.
  1: reflexivity.
  symmetry. etransitivity.
  1: destruct destruct_vector_cons as (? & ? & E). 1: cbn [projT1]. 1: apply Vector.cons_inj in E; inv E.
  1: reflexivity.
  cbn. rewrite skipn_app'. 2: now rewrite length_encode_sym.
  unfold strpush_zero, strpush_common, strpush_common_short.
  cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc.
  cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. reflexivity.
Qed.

Definition strpush_succ (Σ : finType) (s b : Σ) :=
strpush_common s b ++
                     encode_sym
                          (projT1
                             (projT2
                                (FinTypes.finite_n
                                   (finType_CS
                                      (boundary +
                                       sigList (EncodeTapes.sigTape Σ)))))
                             (inr (sigList_X (EncodeTapes.UnmarkedSymbol s)))).

Lemma encode_bsm_succ (Σ : finType) n m s b (t : Vector.t (tape Σ) n) :
      (encode_bsm Σ (encNatTM s b (S m) ::: t)) @[Fin2] = strpush_succ s b ++ (skipn (length (strpush_common_short s b)) ((encode_bsm Σ (encNatTM s b m ::: t))@[Fin2])).
Proof.
  unfold encode_bsm.
  unfold enc_tape. repeat f_equal.
  unfold complete_encode, conv_tape.
  etransitivity.
  1: destruct destruct_vector_cons as (? & ? & E).  1: cbn - [skipn].  1: apply Vector.cons_inj in E; inv E. 1: cbn - [skipn].
  1: unfold strpush_common, strpush_common_short.
  1: destruct_tapes.  1: cbn - [skipn].  1: reflexivity.
  unfold strpush_common, strpush_common_short. cbn - [skipn].
  
  symmetry. etransitivity.  1: cbn - [skipn].
  1: destruct destruct_vector_cons as (? & ? & E). 1: cbn - [skipn]. 1: apply Vector.cons_inj in E; inv E.  1: cbn - [skipn].
  1: destruct_tapes. 1:  cbn - [skipn]. 1:  reflexivity.
  match goal with [|- context [ skipn _ (?x1 ++ true :: false :: ?x2 ++ true :: false :: ?x3 ++ true :: false :: ?x4 ++ ?x5) ]] =>
    replace (x1 ++ true :: false :: x2 ++ true :: false :: x3 ++ true :: false :: x4 ++ x5) with
            ((x1 ++ true :: false :: x2 ++ true :: false :: x3 ++ true :: false :: x4) ++ x5)
  end.
  1: rewrite skipn_app'. 2:{ reflexivity. }
  2:{ rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. reflexivity. }
  unfold strpush_succ, strpush_common, strpush_common_short.
  rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. rewrite <- app_assoc. cbn. reflexivity.
Qed.

Lemma BSM_complete_simulation' n Σ (M : TM Σ n) m i :
{ P |
      (forall q t t', TM.eval M (TM.start M) t q t' ->
       forall v'', BSM.eval (m + (4)) (i, P) (i, Vector.append v'' ((encode_bsm t))) (i + length P, Vector.append v'' ((encode_bsm t')))) /\
      (forall t v'', (exists out, BSM.eval (m + (4)) (i, P) (i, Vector.append v'' ((encode_bsm t))) out) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (KOSBTM_complete_simulation M) as (M1 & Hf1 & Hb1).
  destruct (BSM_addstacks i (SIM M1 i) m ) as (M2 & Hl & Hf2 & Hb2).
  exists M2. split.
  - intros q t t' [q1 H % (SIM_computes i) ] % Hf1.
    intros. eapply Hf2. eapply BSM_sss.eval_iff. split.
    1: cbn [Fin.to_nat proj1_sig mult] in H.  1: rewrite !NPeano.Nat.add_0_l, NPeano.Nat.add_0_r in H.
    1: rewrite <- Hl.  1: rewrite SIM_length.  1: rewrite Nat.mul_comm.  1: eapply H.
    right. unfold fst, subcode.code_end, snd, fst. rewrite <- Hl. lia.
  - intros t v'' (out & [[out1 out2] [Ho1 Ho2]% BSM_sss.eval_iff] % Hb2). eapply Hb1.
    eapply SIM_term with (q := Fin.F1) in Ho2 .
    2:{ cbn [Fin.to_nat proj1_sig mult]. rewrite !NPeano.Nat.add_0_l, NPeano.Nat.add_0_r. eapply Ho1. }
    destruct Ho2 as (q' & t' & H1 & -> & H2). eauto.
Qed.

Lemma BSM_complete_simulation n Σ (M : TM Σ n) m  i :
{ P |
      (forall q t t', TM.eval M (TM.start M) t q t' ->
       forall v'', BSM.eval (m + (4)) (i, P) (i, Vector.append v'' ((encode_bsm t))) (i + length P, Vector.append v'' ((encode_bsm t')))) /\
      (forall t v'', (sss.sss_terminates (bsm_sss (n := (m + (4)))) (i, P) (i, Vector.append v'' ((encode_bsm t)))) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (@BSM_complete_simulation' n Σ M m i) as (P & H1 & H2).
  exists P. split.  1: exact H1.
  intros t v'' ([out1 out2] & H % BSM_sss.eval_iff). eapply H2. eauto.
Qed.

Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).

Lemma pos_right_inj {n m} p q :
  @pos_right n m p = @pos_right n m q -> p = q.
Proof.
  induction n in p, q |- *; cbn in *.
  - eauto.
  - intros. eapply IHn, pos_nxt_inj, H.
Qed.

Lemma vec_pos_const {k} {X x} (p : pos k) : vec_pos (@Vector.const X x k) p = x.
Proof.
  induction p; cbn; eauto.
Qed.


Lemma Fin4_cases (P : pos 4 -> Prop) :
   P Fin0 -> P Fin1 -> P Fin2 -> P Fin3 -> forall p, P p.
Proof.
  intros H0 H1 H2 H3.
  repeat (intros p; eapply (Fin.caseS' p); clear p; [ eauto | ]).
  intros p. inversion p.
Qed.

Lemma PREP1_spec k Σ n :
{ PREP1 : list (bsm_instr ((1 + k) + 4)) | forall v : Vector.t nat k,
    (0, PREP1) // (0, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) (Vector.const [] 4)) ->>
                  (length PREP1, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) ((@encode_bsm Σ _ (Vector.const niltape n)))) }.
Proof.
  exists (push_exactly (pos_right (1 + k) Fin0) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin0])
       ++ push_exactly (pos_right (1 + k) Fin1) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin1])
       ++ push_exactly (pos_right (1 + k) Fin2) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin2])
       ++ push_exactly (pos_right (1 + k) Fin3) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin3])).
  intros v.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin0) 0 ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin0])). 1:auto.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin1) _ ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin1])). 1:auto.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin2) _ ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin2])). 1:auto.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin3) _ ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin3])). 1:auto.
  bsm sss stop. f_equal.
  1:rewrite !app_length; lia.
  eapply vec_pos_ext. eapply pos_left_right_rect.
  - rewrite <- !vec_app_spec. symmetry. rewrite vec_pos_app_left.
    rewrite !vec_change_neq; auto.
    now rewrite vec_pos_app_left.
  - rewrite <- !vec_app_spec. rewrite !vec_pos_app_right.
    intros p; eapply (Fin.caseS' p); clear p.
    1:{ repeat (rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence]).
        rewrite vec_change_eq; [ | auto]. rewrite vec_pos_app_right.
        now rewrite vec_pos_const, app_nil_r, vec_pos_spec. }
    intros p; eapply (Fin.caseS' p); clear p.
    1:{ rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_eq; [ | auto]. rewrite vec_pos_app_right.
        rewrite vec_pos_const. rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite vec_pos_app_right. now rewrite vec_pos_const, app_nil_r, vec_pos_spec. }
    intros p; eapply (Fin.caseS' p); clear p.
    1:{ rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        rewrite vec_change_eq; [ | auto]. rewrite vec_pos_app_right.
        rewrite vec_pos_const. rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite vec_pos_app_right. now rewrite vec_pos_const, app_nil_r, vec_pos_spec. }
    intros p; eapply (Fin.caseS' p); clear p.
    1:{ rewrite vec_change_eq; [ | auto]. rewrite vec_pos_app_right.
        rewrite vec_pos_const. rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite vec_pos_app_right. now rewrite vec_pos_const, app_nil_r, vec_pos_spec. }
    intros p. inversion p.
Qed.

Lemma vec_map_spec {X Y n} (v : Vector.t X n) (f : X -> Y) :
  vec_map f v = Vector.map f v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma pos_left_inj {n m} p q :
  @pos_left n m p = @pos_left n m q -> p = q.
Proof.
  induction p in q |- *; cbn in *.
  - eapply (Fin.caseS' q).
    + reflexivity.
    + clear q. cbn. congruence.
  - eapply (Fin.caseS' q).
    + cbn. congruence.
    + clear q. cbn. intros. f_equal. eapply IHp.
      now eapply pos_nxt_inj.
Qed.

Lemma PREP2_spec'' k (Σ : finType) (x : pos k) i s b :
{ PREP2 : list (bsm_instr ((1 + k) + 4)) | length PREP2 = 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)) /\
forall v : Vector.t (list bool) k,  forall n, forall t : Vector.t (tape Σ) n, forall m m',
   v @[x] = repeat true m ->
    (i, PREP2) // (i,                Vector.append ([] ::: v) ((@encode_bsm Σ _ (encNatTM s b m' ::: t)))) ->>
                  (i + length PREP2, Vector.append ([] ::: vec_change v x nil) ((@encode_bsm Σ _ (encNatTM s b (m + m') ::: t)))) }.
Proof.
  exists (POP (pos_left 4 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)))
       :: pop_many (pos_right (1 + k) Fin2) (length (strpush_common_short s b)) (1 + i)
       ++ push_exactly (pos_right (1 + k) Fin2) (strpush_succ s b)
       ++ POP (pos_left 4 Fin0) 0 i :: nil). split.
  { cbn. rewrite !app_length. cbn. rewrite pop_many_length, push_exactly_length. lia. }
  intros v n t m m' Hx.
  induction m in v, m', Hx |- *.
  - bsm sss POP empty with (pos_left 4 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b))).
  1: rewrite <- !vec_app_spec, vec_pos_app_left.  1: cbn in *.
  1: rewrite vec_pos_spec, Hx.  1: reflexivity.
    bsm sss stop. f_equal.  1: cbn.  1: rewrite !app_length.  1: cbn.  1: rewrite pop_many_length, push_exactly_length.  1: lia. cbn in Hx.
    rewrite <- Hx. now rewrite <- vec_pos_spec, vec_change_same.
  - bsm sss POP one with (pos_left 4 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b))) (repeat true m).
    1:{ rewrite <- !vec_app_spec, vec_pos_app_left. cbn.
        rewrite vec_pos_spec, Hx. reflexivity. }
    eapply subcode_sss_compute_trans. 2: eapply (pop_many_spec (pos_right (1 + k) Fin2) (length (strpush_common_short s b)) (1 + i)). 1:auto.
    eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin2) _ (strpush_succ s b)).
    { eexists (POP _ _ _ :: pop_many _ _ _), ([POP _ _ _]). split.
    1: simpl_list.  1: cbn.  1: simpl_list.  1: reflexivity.
      cbn; rewrite pop_many_length. lia.
    }
    bsm sss POP empty with (pos_left 4 Fin0) 0 i. {
      eexists (POP _ _ _ :: pop_many _ _ _ ++ push_exactly _ _), []. simpl_list. cbn. simpl_list. cbn. split.  1: reflexivity.
      rewrite pop_many_length, push_exactly_length. lia. }
    specialize IHm with (m' := (S m')). replace (S m + m') with (m + S m') by lia.
    match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : Vector.t (list bool) ((1 + k) + 4)); enough (st = ev) as ->; subst ev end.
    1: match goal with [ |- sss_compute _ _ _ (_, ?st) ] => evar (ev : Vector.t (list bool) ((1 + k) + 4)); enough (st = ev) as ->; subst ev end.
    1: eapply IHm with (v := vec_change v x (repeat true m)).  1: now rewrite <- vec_pos_spec, vec_change_eq.  1: now rewrite vec_change_idem.
    rewrite <- !vec_app_spec.
    eapply vec_pos_ext. eapply pos_left_right_rect.
    + symmetry. rewrite vec_pos_app_left.
      rewrite vec_change_neq; auto.
      rewrite vec_change_neq; auto. cbn in p.
      eapply (Fin.caseS' p); clear p.  1: cbn.  1: reflexivity.
      intros p.
      destruct (pos_eq_dec p x).
      * rewrite vec_change_eq. 2: now subst. cbn. subst. now rewrite vec_change_eq.
      * rewrite vec_change_neq. 2: intros ? % pos_left_inj % pos_nxt_inj; eauto.
        rewrite vec_pos_app_left.  cbn. rewrite vec_change_neq; eauto.
    + intros p. symmetry. rewrite !vec_pos_app_right. symmetry.
      rewrite !vec_change_idem.
      revert p.
      apply Fin4_cases.
      * repeat (rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence]).
          rewrite vec_change_neq; [ | eapply pos_right_left]. rewrite vec_pos_app_right.
          now rewrite !vec_pos_spec, !encode_bsm_at0.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | auto].
        now rewrite vec_pos_app_right, !vec_pos_spec, !encode_bsm_at1.
      * rewrite vec_change_eq; auto.
        rewrite vec_change_eq; eauto.
        rewrite vec_change_neq; eauto.
        rewrite vec_pos_app_right.
        now rewrite !vec_pos_spec, encode_bsm_succ.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | auto].
        now rewrite vec_pos_app_right, !vec_pos_spec, !encode_bsm_at3.
Qed.

Definition PREP2''_length (Σ : finType) (s b : Σ) := proj1_sig (encode_bsm_zero s b) + length (strpush_zero s b) + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)).

Lemma PREP2_spec' k (Σ : finType) (x : pos k) i s b n :
{ PREP2 : list (bsm_instr ((1 + k) + 4)) | length PREP2 = PREP2''_length s b  /\
forall v : Vector.t (list bool) k, forall t : Vector.t (tape Σ) n, forall m,
   v @[x] = repeat true m ->
    (i, PREP2) // (i,                Vector.append ([] ::: v) ((@encode_bsm Σ _ t))) ->>
                  (i + length PREP2, Vector.append ([] ::: vec_change v x nil) ((@encode_bsm Σ _ (encNatTM s b m ::: t)))) }.
Proof.
  unfold PREP2''_length.
  destruct (encode_bsm_zero s b) as [n' Hn'].
  destruct (PREP2_spec'' x (i + n' + length (strpush_zero s b)) s b) as [PREP2 [Hl2 H]].
  exists (pop_many (pos_right (1 + k) Fin2) n' i
       ++ push_exactly (pos_right (1 + k) Fin2) (strpush_zero s b)
       ++ PREP2). split.
  {  cbn. rewrite !app_length. cbn. rewrite pop_many_length, push_exactly_length. cbn in Hl2. rewrite Hl2. lia. }
  intros v t m Hm.
  eapply subcode_sss_compute_trans. 2: eapply (pop_many_spec (pos_right (1 + k) Fin2) n' i). 1:auto.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin2) _ (strpush_zero s b)).
  { eexists (pop_many _ _ _), PREP2. split.  1: reflexivity. rewrite pop_many_length. lia. }
  specialize H with (m' := 0) (v := v) (1 := Hm). replace (m + 0) with m in H by lia.
  eapply subcode_sss_compute_trans. 2:{
  match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : Vector.t (list bool) ((1 + k) + 4)); enough (st = ev) as ->; subst ev end.
  1: match goal with [ |- sss_compute _ _ (?st, _) _ ] => evar (ev : nat); enough (st = ev) as ->; subst ev end.
  - eapply H.
  - rewrite push_exactly_length. lia.
  - eapply vec_pos_ext. eapply pos_left_right_rect.
    + intros p. rewrite <- !vec_app_spec, !vec_pos_app_left.
      rewrite vec_change_neq; auto.
      rewrite vec_change_neq; auto. now rewrite vec_pos_app_left.
    + rewrite <- !vec_app_spec. eapply Fin4_cases.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
        rewrite !vec_pos_app_right.
        rewrite !vec_pos_spec. now rewrite !encode_bsm_at0.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
        now rewrite !vec_pos_app_right, !vec_pos_spec, !encode_bsm_at1.
      * rewrite vec_change_eq; auto.
        rewrite vec_change_eq; eauto.
        rewrite !vec_pos_app_right.
        now rewrite !vec_pos_spec, Hn'.
      * rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
        now rewrite !vec_pos_app_right, !vec_pos_spec, !encode_bsm_at3.
  }
  { eexists (pop_many _ _ _ ++ push_exactly _ _), []. rewrite app_nil_r. split.  1: now simpl_list. rewrite app_length, pop_many_length, push_exactly_length. lia. }
  bsm sss stop. f_equal.
  rewrite !app_length, pop_many_length, push_exactly_length. lia.
Qed.

Definition BSM_cast {n} (P : list (bsm_instr n)) {m} (E : n = m) : list (bsm_instr m).
subst m. exact P. Defined.

Lemma BSM_cast_length {n} (P : list (bsm_instr n)) {m} (E : n = m) :
  length (BSM_cast P E) = length P.
Proof.
  destruct E. cbn. reflexivity.
Qed.

Lemma BSM_cast_spec {n m} i (P : list (bsm_instr n)) (E : n = m) j v k w :
   sss.sss_compute (@bsm_sss _) (i, P) (j, v) (k, w) <-> sss.sss_compute (@bsm_sss _) (i, BSM_cast P E) (j, Vector.cast v E) (k, Vector.cast w E).
Proof.
  destruct E. cbn. now rewrite !cast_eq_refl.
Qed.

Fixpoint PREP2' (Σ : finType) (s b : Σ) k'' (k' : nat)  (i : nat) (n : nat) : list (bsm_instr ((1 + (k' + k'') + 4))).
Proof.
  destruct k'.
  - exact List.nil.
  - refine (List.app _ (BSM_cast (PREP2' Σ s b (S k'') k' (i + PREP2''_length s b) n) _)). 2:abstract lia.
    assert (k' < S k' + k'') as Hn by abstract lia.
    refine (proj1_sig (@PREP2_spec' (S k' + k'') Σ (Fin.of_nat_lt Hn) i s b (k'' + n))).
Defined.

Lemma PREP2'_length (Σ : finType) (s b : Σ) k (k' : nat) (i : nat) n :
  | @PREP2' Σ s b k k' i n| = k' * PREP2''_length s b.
Proof.
  induction k' in k, i |- *.
  - cbn. reflexivity.
  - cbn - [mult]. destruct PREP2_spec' as (? & ? & ?). cbn. rewrite app_length. cbn in e. rewrite e. cbn in IHk'.
    rewrite BSM_cast_length. rewrite IHk'. lia.
Qed.

Notation "v1 +++ v2" := (Vector.append v1 v2) (at level 60).

Lemma vec_list_encode_bsm Σ n1 n2 v1 v2 :
vec_list v1 = vec_list v2 ->
 vec_list (@encode_bsm Σ n1 v1) = vec_list (@encode_bsm Σ n2 v2).
Proof.
  intros H.
  assert (n1 = n2).  1: eapply (f_equal (@length _)) in H.  1: rewrite !vec_list_length in H.  1: eauto.
  subst. eapply vec_list_inj in H. now subst.
Qed.

Lemma PREP2_spec_strong (Σ : finType) i s b k' k'' v (v' : Vector.t nat k'') n (t : Vector.t (tape Σ) n) :
    (i, @PREP2' Σ s b k'' k'  i n) //
        (i,                                            ([] ::: Vector.map (fun n => repeat true n) v +++ Vector.const [] k'') +++  (@encode_bsm Σ _ (Vector.map (encNatTM s b) v' +++ t))) ->>
        (i + length(@PREP2' Σ s b k'' k' i n), ([] ::: Vector.const [] (k' + k'')  +++  (@encode_bsm Σ _ (Vector.map (encNatTM s b) (v +++ v') +++ t)))).
Proof.
  induction k' in k'', v, v', i |- *.
  - cbn. bsm sss stop. f_equal.  1: lia. f_equal. revert v. eapply (Vector.case0). cbn. reflexivity.
  - unshelve edestruct (vector_inv_back v) as [(y, vl) Hv].  1: abstract lia. cbn - [minus mult].
    assert (k' < S k') as Hlt by lia.
    match goal with [ |- context[proj1_sig ?y]] => destruct y as [PREPIT [HlP HPREP]]; cbn [proj1_sig] end.
    eapply subcode_sss_compute_trans with (P := (i, _)). { cbn - [minus mult]. eexists [], _. cbn - [mult minus]. split.  1: reflexivity. cbn; now rewrite NPeano.Nat.add_0_r. }
    1: cbn - [minus mult].  1: cbn - [minus mult] in HPREP.  1: specialize HPREP with (m := v@[Fin.of_nat_lt Hlt]).  1: cbn [mult] in HPREP.
    Arguments Fin.of_nat_lt _ {_ _}.  1: refine (HPREP _ _ _). { rewrite <- !vec_pos_spec, <- !vec_map_spec, <- !vec_app_spec. eapply nth_error_vec_list.
    rewrite @vec_list_vec_app with (n := S k') (m := k''), vec_list_vec_map.
    rewrite nth_error_app1. 2: rewrite map_length, vec_list_length; lia.
    eapply map_nth_error.
    erewrite nth_error_vec_list.
    all:eapply nth_error_nth'; rewrite vec_list_length ;lia.
    }
    pose proof (@vec_list_vec_map nat (list bool)) as Heq. specialize (Heq) with (n := (S (k' + k''))).
    match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : vec (list bool) (S (S (k' + k'' + 4)))); enough (st = ev) as ->; subst ev end.
    1: match goal with [ |- sss_compute _ _ _ (_, ?st) ] => evar (ev : vec (list bool) (S (S (k' + k'' + 4)))); enough (st = ev) as ->; subst ev end.
    1: match goal with [ |- sss_compute _ _ _ (?st, _) ] => evar (ev : nat); enough (st = ev) as ->; subst ev end.
    1: cbn - [minus mult] in HlP.  1: rewrite <- HlP.
    1: eapply subcode_sss_compute with (P := (i + |PREPIT|, _)). { exists PREPIT, []. split. 2:reflexivity. now simpl_list. }
    1: specialize IHk' with (v := vl) (v' := y ::: v') (k'' := S k'').  1: apply BSM_cast_spec.
    1: eapply IHk'.
    + rewrite !app_length, BSM_cast_length, !PREP2'_length.
      setoid_rewrite PREP2'_length. lia.
    + cbn. cbn. f_equal. eapply vec_list_inj.
      rewrite <- !vec_map_spec, <- !vec_app_spec. cbn [vec_list]. rewrite !vec_list_cast, !vec_list_vec_app, !vec_list_const.
      rewrite app_comm_cons. f_equal.
      1: now replace  (k' + S k'') with (S (k' + k'')) by lia. f_equal. subst v.
      rewrite !vec_app_spec. setoid_rewrite vec_map_spec.
      rewrite !Vector_map_app.
      pose proof (@Vector_map_app) as Vm. specialize Vm with (k1 := S k') (k2 := k''). cbn in Vm. rewrite Vm. clear Vm.
      eapply vec_list_inj, vec_list_encode_bsm.
      rewrite <- !vec_map_spec, <- !vec_app_spec.
      rewrite !vec_list_vec_app.
      setoid_rewrite <- vec_map_spec. rewrite !vec_list_vec_map. cbn[vec_list map].
      pose proof (@vec_list_vec_app (tape Σ) (S (k' + k'')) n). cbn [plus] in H. rewrite H. clear H.
      pose proof (@vec_list_vec_app (tape Σ) (S k') k''). cbn [plus] in H. rewrite H. clear H.
      rewrite !vec_list_vec_map. cbn[vec_list map]. simpl_list.
      rewrite !vec_list_cast. cbn. simpl_list. rewrite vec_list_vec_app. cbn. simpl_list. reflexivity.
    + eapply vec_list_inj. rewrite <- !vec_map_spec, <- !vec_app_spec. cbn [vec_list].
      rewrite !vec_list_cast.
       pose proof (@vec_list_vec_app (list bool) (S (k' + k'')) 4). cbn [plus] in H. rewrite !H. clear H.
       pose proof (@vec_list_vec_app (list bool) (S (k' + S k'')) 4). cbn [plus] in H. rewrite !H. clear H.
       cbn [vec_list app]. f_equal. rewrite !vec_list_vec_app.
       cbn [Vector.map]. rewrite vec_app_cons. f_equal. 2:{ f_equal. f_equal. f_equal.
       subst v. f_equal. rewrite <- vec_pos_spec. eapply nth_error_vec_list.
       rewrite vec_list_cast, <- vec_app_spec, vec_list_vec_app, nth_error_app2; rewrite !vec_list_length, ?Nat.sub_diag; try lia.
       reflexivity. }
       rewrite vec_list_vec_change.
       pose proof (@vec_list_vec_app (list bool) (S k') k''). cbn [plus] in H. rewrite !H. clear H.
       setoid_rewrite <- vec_map_spec.
       rewrite !vec_list_vec_map, !vec_list_const.
       rewrite update_app_left. 2: rewrite Fin.to_nat_of_nat; cbn; rewrite map_length, vec_list_length; lia.
       subst v. rewrite vec_list_cast. rewrite <- vec_app_spec. rewrite vec_list_vec_app. cbn [vec_list]. rewrite Fin.to_nat_of_nat. cbn.
       rewrite map_app, update_app_right.  2: rewrite map_length, vec_list_length; lia.
       rewrite map_length, vec_list_length, Nat.sub_diag. cbn. now simpl_list.
    Unshelve. exact 0.
Qed.

Lemma PREP2_spec k (Σ : finType) i s b  n :
  { PREP2 | forall v (t : Vector.t (tape Σ) n),
    (i, PREP2) //
        (i,                               ([] ::: Vector.map (fun n => repeat true n) v) +++  (@encode_bsm Σ _ t)) ->>
        (i + length PREP2, ([] ::: Vector.const [] k                      +++  (@encode_bsm Σ _ (Vector.map (encNatTM s b) v +++ t)))) }.
Proof.
  unshelve eexists (BSM_cast (@PREP2' Σ s b 0 k  i n) _).  1: abstract lia. intros v t.
  match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : vec (list bool) (S k + 4)); enough (st = ev) as ->; subst ev end.
  1: match goal with [ |- sss_compute _ _ _ (_, ?st) ] => evar (ev : vec (list bool) (S k + 4)); enough (st = ev) as ->; subst ev end.
  1: rewrite <- BSM_cast_spec.
  1: rewrite BSM_cast_length.  1: eapply PREP2_spec_strong.
    - eapply vec_list_inj.
      rewrite <- !vec_app_spec. cbn. rewrite vec_list_cast, !vec_list_vec_app, !vec_list_const.
      f_equal. f_equal.  1: now rewrite NPeano.Nat.add_0_r.
      eapply vec_list_encode_bsm. Unshelve. 3: exact [| |]. 2: exact v. 2: exact t.
      rewrite <- !vec_map_spec, !vec_list_vec_app, !vec_list_vec_map, !vec_list_vec_app. cbn. now rewrite app_nil_r.
    - eapply vec_list_inj.
      rewrite <- !vec_app_spec, <- !vec_map_spec, !vec_app_cons, vec_list_cast.
      cbn. f_equal. rewrite !vec_list_vec_app. f_equal.  1: cbn.  1: now simpl_list.
      eapply vec_list_encode_bsm. f_equal.
      eapply vec_pos_ext. intros. now rewrite vec_pos_set.
Qed.

Lemma PREP3_spec k n Σ i :
  { PREP3 | forall v : Vector.t (list bool) k, forall t : Vector.t _ n,
    (i, PREP3) // (i, v +++ @encode_bsm Σ _ t) ->>
                  (i + length PREP3, v +++ (@encode_bsm Σ _ (niltape ::: t)))
  }.
Proof.
  edestruct (@encode_bsm_nil Σ n) as ([str n'] & H).
  exists (pop_many (pos_right k Fin2) n' i
      ++ push_exactly (pos_right k Fin2) str).
  intros v t.
  eapply subcode_sss_compute_trans with (P := (i, pop_many (pos_right k Fin2) n' i)).  1: auto.
  1: eapply pop_many_spec.
  eapply subcode_sss_compute_trans with (P := (n' + i, push_exactly (pos_right k Fin2) str)).
  { exists (pop_many (pos_right k Fin2) n' i), []. split.  1: now rewrite app_nil_r. rewrite pop_many_length; lia. }
  1: eapply push_exactly_spec. bsm sss stop.
  f_equal.  1: rewrite app_length, pop_many_length, push_exactly_length; lia.
  rewrite !vec_change_idem.
  rewrite vec_change_eq; auto.
  rewrite <- !vec_app_spec.
  rewrite vec_pos_app_right.
  eapply vec_pos_ext.  eapply pos_left_right_rect.
  - intros p. rewrite vec_pos_app_left.
    rewrite vec_change_neq; auto. now  rewrite vec_pos_app_left.
  - eapply Fin4_cases.
    + rewrite !vec_pos_app_right.
      rewrite vec_change_neq; [ | intros ? % pos_right_inj; congruence].
      rewrite vec_pos_app_right. now rewrite !vec_pos_spec, !encode_bsm_at0.
    + rewrite !vec_pos_app_right.
      rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj; congruence].
      rewrite vec_pos_app_right. now rewrite !vec_pos_spec, !encode_bsm_at1.
    + rewrite !vec_pos_app_right.
      rewrite vec_change_eq; auto.
      now rewrite !vec_pos_spec, H.
    + rewrite !vec_pos_app_right.
      rewrite vec_change_neq; [ | intros ? % pos_right_inj % pos_nxt_inj % pos_nxt_inj; congruence].
      rewrite vec_pos_app_right. now rewrite !vec_pos_spec, !encode_bsm_at3.
Qed.

Lemma PREP_spec k n Σ s b :
  { PREP | forall v : Vector.t nat k,
    (0, PREP) // (0, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) (Vector.const [] 4)) ->>
                                           (length PREP, Vector.append (Vector.const [] (1 + k)) ((@encode_bsm Σ _ (Vector.append (niltape ::: Vector.map (encNatTM s b) v)
                                           (Vector.const niltape n)))))
  }.
Proof.
  destruct (PREP1_spec k Σ n) as [PREP1 H1].
  destruct (@PREP2_spec k Σ (length PREP1) s b n) as [PREP2 H2].
  destruct (@PREP3_spec (1 + k) (k + n) Σ (length PREP1 + length PREP2)) as [PREP3 H3].
  exists (PREP1 ++ PREP2 ++ PREP3).
  intros v.
  eapply subcode_sss_compute_trans. 2: eapply H1.  1: auto.
  eapply subcode_sss_compute_trans. 2: eapply H2.  1: auto.
  eapply subcode_sss_compute_trans. 2: specialize H3 with (v := [] ## Vector.const [] k); apply H3.  1: auto.
  bsm sss stop. f_equal. rewrite !app_length. now rewrite Nat.add_assoc.
Qed.

Lemma skipn_plus n m {X} (l : list X) : skipn n (skipn m l) = skipn (n + m) l.
Proof.
  induction m in n, l |- *.
  - cbn. f_equal. lia.
  - cbn. destruct l.  1: cbn.  1: destruct n; reflexivity. rewrite IHm. now replace (n + S m) with (S n + m) by lia.
Qed.
    

Lemma POSTP_spec' k n (Σ : finType) s b i :
  { POSTP | forall v : Vector.t _ k, forall t : Vector.t (tape Σ) (k + n), forall m m', exists out,
   (i, POSTP) // (i, Vector.append (repeat true m' ## v) ([] ::: [false] ::: skipn (length (strpush_common s b)) ((encode_bsm (encNatTM s b m ## t))@[Fin2]) ::: [] ::: vec_nil)) ->>
                 (i + length POSTP, Vector.append (repeat true (m + m') ## v) (out ))
  }.
Proof.
  pose (THESYM := encode_sym
  (projT1
     (projT2
        (FinTypes.finite_n
           (finType_CS
              (boundary +
               sigList (EncodeTapes.sigTape Σ)))))
     (inr (sigList_X (EncodeTapes.UnmarkedSymbol s))))).
  exists (pop_exactly (pos_right (1 + k) Fin2) (pos_right (1 + k) Fin0) (i + 4 + 2 * length THESYM) THESYM i
      ++  PUSH (pos_left 4 Fin0) true
      ::  pop_many (pos_right (1 + k) Fin2) 2 (i + 1 + 2 * length THESYM)
      ++  POP (pos_right (1 + k) Fin0) i i :: nil).
  intros.
  induction m in i, m' |- *.
  - pose proof (encode_bsm_zero s b) as [n' Hn'].
    rewrite Hn'. unfold strpush_zero. rewrite <- !app_assoc.
    rewrite skipn_app'; [ | reflexivity].
    edestruct (@pop_exactly_spec2 (1 + k + 4) (pos_right (1 + k) Fin2) (pos_right (1 + k) Fin0) (i + 4 + 2 * length THESYM)) as [x' Hpop].
    1:{ intros ? % pos_right_inj; congruence. }
    3:{ eexists. eapply subcode_sss_compute_trans. 2: eapply Hpop.  1: auto.  1: eexists [], _.  1: cbn.  1: split. 2: lia.  1: repeat f_equal.
        bsm sss stop. f_equal.  1: rewrite !app_length, pop_exactly_length.  1: cbn - [mult].  1: lia.
        rewrite <- !vec_app_spec.
        rewrite vec_change_app_right. reflexivity.
    }
    2:{ rewrite <- !vec_app_spec.
       rewrite vec_pos_app_right. reflexivity. }
       rewrite <- !vec_app_spec.
       rewrite vec_pos_app_right. cbn.
    intros (l' & Hneq).
     unfold THESYM in Hneq. eapply utils_list.list_app_inj in Hneq as [].
     2: now rewrite !length_encode_sym. eapply encode_sym_inj in H.
     destruct FinTypes.finite_n as ( ? & f & g & H1 & H2); cbn in H.
     eapply (f_equal g) in H. rewrite !H2 in H. easy.
  - edestruct IHm as [out IH]. eexists.
    rewrite encode_bsm_succ. unfold strpush_succ. rewrite <- !app_assoc.
    rewrite skipn_app'; try reflexivity.
    fold THESYM.
    eapply subcode_sss_compute_trans. 2: eapply pop_exactly_spec1. { eexists [], _. split. 2:cbn;lia. { cbn.  f_equal. } }
    1:{ intros ? % pos_nxt_inj % pos_right_inj. congruence. }
    1: cbn.  1: rewrite <- !vec_app_spec.  1: rewrite vec_pos_app_right.  1: cbn.  1: reflexivity.
    1: cbn.  1: rewrite <- !vec_app_spec.  1: rewrite vec_pos_app_right.  1: cbn.  1: reflexivity.
    rewrite <- !vec_app_spec. rewrite vec_app_cons. cbn [vec_change pos_S_inv]. rewrite vec_change_app_right. cbn [vec_change pos_S_inv].
    bsm sss PUSH with  (pos_left 4 Fin0) true.  1: eexists (pop_exactly (pos_right (1 + k) pos2) (pos_right (1 + k) pos0)
    (i + 4 + 2 * (| THESYM |)) THESYM i), _.  1: cbn.  1: split.  1: repeat f_equal.   1: rewrite pop_exactly_length.  1: lia.

    
    rewrite <- vec_app_cons. rewrite vec_change_app_left. cbn [vec_change pos_S_inv]. rewrite vec_pos_app_left. cbn [vec_pos pos_S_inv].
    eapply subcode_sss_compute_trans. 2: eapply (@pop_many_spec (1 + k + 4) (pos_right (1 + k) Fin2) 2).
    { eexists (pop_exactly (pos_right (1 + k) Fin2) (pos_right (1 + k) Fin0) (i + 4 + 2 * length THESYM) THESYM i
    ++  PUSH (pos_left 4 Fin0) true :: nil), (POP (pos_right (1 + k) Fin0) i i :: nil). split.  1: simpl_list.  1: repeat f_equal.  1: cbn - [mult].  1: repeat f_equal. 1-4: cbn; lia.
    rewrite app_length, pop_exactly_length. cbn. lia. }
    rewrite vec_change_app_right. cbn [vec_change pos_S_inv]. rewrite vec_pos_app_right.
    cbn [vec_pos pos_S_inv]. rewrite skipn_plus.
    bsm sss POP empty with (pos_right (1 + k) Fin0) i i.  1: eexists (_ ++ _ :: _), [].  1: split.  1: rewrite app_nil_r.  1: simpl_list.  1: reflexivity.  1: rewrite app_length, pop_exactly_length.
    1: cbn.  1: lia.  1: now rewrite vec_pos_app_right.
    

    match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : Vector.t (list bool) ((1 + k) + 4)); enough (st = ev) as ->; subst ev end.
    1: match goal with [ |- sss_compute _ _ (_, _) (_, ?st) ] => evar (ev : Vector.t (list bool) ((1 + k) + 4)); enough (st = ev) as ->; subst ev end.
    1: eapply IH.  1: instantiate (1 := S m').  1: replace (m + S m') with (S (m + m')).  1: cbn [repeat plus].  1: rewrite vec_app_cons.
    1: now rewrite vec_app_spec.  1: lia.
    cbn [repeat]. rewrite vec_app_spec. repeat f_equal. unfold strpush_common. rewrite app_length. cbn. lia.
Qed.

Lemma encode_bsm_ext Σ n v :
  @encode_bsm Σ n v = [] ::: [false] ::: (encode_bsm v @[Fin2]) ::: [] ::: vec_nil.
Proof.
  eapply vec_pos_ext. eapply Fin4_cases.
  - now rewrite vec_pos_spec, encode_bsm_at0.
  - now rewrite vec_pos_spec, encode_bsm_at1.
  - reflexivity.
  - now rewrite vec_pos_spec, encode_bsm_at3.
Qed.

Lemma POSTP_spec k n (Σ : finType) s b i :
  { POSTP | forall v : Vector.t _ k, forall t : Vector.t (tape Σ) (k + n), forall m, exists out,
   (i, POSTP) // (i, Vector.append ([] ## v) ((encode_bsm (encNatTM s b m ## t)))) ->>
                                            (i + length POSTP, Vector.append (repeat true m ## v) (out ))
  }.
Proof.
  destruct (@POSTP_spec' k n Σ s b (i + (length (strpush_common s b)))) as [POSTP HPOST].
  specialize HPOST with (m' := 0).
  exists (pop_many (pos_right (1 + k) Fin2) (length (strpush_common s b)) i
      ++  POSTP).
  intros v t m. specialize HPOST with (m := m).
  edestruct (HPOST v) as (out & HPOST').
  exists out.
  eapply subcode_sss_compute_trans. 2: eapply pop_many_spec. { eexists [], _. cbn. split.  1: reflexivity. lia. }
  rewrite <- !vec_app_spec. rewrite vec_app_cons. cbn [vec_change pos_S_inv].
  rewrite vec_change_app_right. cbn [vec_change pos_S_inv].
  rewrite encode_bsm_ext. cbn [vec_pos vec_change pos_S_inv]. rewrite vec_pos_app_right.
  cbn [vec_pos vec_change pos_S_inv].
  rewrite vec_app_spec. cbn [Vector.append] in *.
  rewrite vec_app_cons.
  rewrite NPeano.Nat.add_0_r in HPOST'. rewrite vec_app_spec. cbn [repeat] in HPOST'.
  replace (|strpush_common s b| + i) with (i + |strpush_common s b|) by lia.
  eapply subcode_sss_compute_trans.
  2: apply HPOST'.  1: eexists _, [].  1: split.  1: now rewrite app_nil_r.  1: rewrite pop_many_length.  1: lia.
  bsm sss stop. f_equal. rewrite app_length, pop_many_length. cbn. lia.
Qed.

Theorem TM_computable_to_BSM_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  TM_computable R -> BSM_computable R.
Proof.
  intros (n & Σ & s & b & Hsb & M & HM1 & HM2) % TM_computable_iff.
  destruct (@PREP_spec k n Σ s b) as [PREP HPREP].
  destruct (BSM_complete_simulation M (1 + k) (length PREP)) as (Mbsm & Hf & Hb).
  destruct (@POSTP_spec k n Σ s b (length (PREP ++ Mbsm))) as [POSTP HPOSTP].
  eapply BSM_computable_iff.
  eexists. exists 0. exists (PREP ++ Mbsm ++ POSTP). split.
  - intros v m (q & t & Heval & Hhd)% HM1. eapply Hf in Heval.
    cbn in t. destruct_tapes. cbn in Hhd. subst.
    eapply BSM_sss.eval_iff in Heval.
    setoid_rewrite BSM_sss.eval_iff. fold plus.
    edestruct (HPOSTP) as [out HPOSTP'].
    eexists. eexists.
    split.
    + eapply subcode_sss_compute_trans with (P := (0, PREP)). 1:auto.
    1: eapply HPREP.
      eapply subcode_sss_compute_trans with (P := (|PREP|, Mbsm)). 1:auto.
      1: eapply Heval.
      eapply subcode_sss_compute_trans with (P := (|PREP ++ Mbsm|, POSTP)). 1:auto.
      1: rewrite <- app_length.  1: eapply HPOSTP'.
      bsm sss stop. reflexivity.
    + cbn. right. rewrite !app_length. lia.
  - intros. edestruct Hb as (? & ? & HbH). 2:eapply HM2. 2:eapply HbH.
    eapply subcode_sss_terminates.
    2:{ eapply subcode_sss_terminates_inv.  1: eapply bsm_sss_fun.
    1: eapply H. 2:{ split.  1: eapply HPREP. cbn. lia. } auto. }
    auto.
Qed.
