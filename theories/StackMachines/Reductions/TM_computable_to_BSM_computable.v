Set Default Goal Selector "!".

Require Import 
  Undecidability.StackMachines.BSM Undecidability.StackMachines.Util.BSM_computable
  Undecidability.TM.TM Undecidability.TM.Util.TM_facts Undecidability.TM.Util.TM_computable.
From Undecidability.StackMachines Require Import SBTM_HALT_to_HaltBSM.
From Undecidability.TM Require Import TM Arbitrary_to_Binary mTM_to_TM HaltTM_1_to_SBTM_HALT.
From Undecidability.Shared.Libs.DLW Require Import vec pos sss subcode.
From Undecidability Require Import bsm_utils bsm_defs.
Require Import Undecidability.TM.Code.Code.
From Undecidability.Shared.Libs.PSL Require FinTypes.
From Undecidability.TM Require Import Single.EncodeTapes.
From Undecidability.TM Require Import SBTM.
From Undecidability.StackMachines Require Import BSM BSM.bsm_defs.

Create HintDb vec_simpl discriminated.

Hint Rewrite vec_change_eq using easy : vec_simpl.
Hint Rewrite vec_change_neq using easy : vec_simpl.

Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Notation "P // s ~~> t" := (sss_output (@bsm_sss _) P s t).

(*--- Utility ---*)

Notation "v @[ t ]" := (Vector.nth v t).
Local Hint Rewrite map_app  : list.

Lemma skipn_app' (X : Type) (xs ys : list X) (n : nat) :
  n = (| xs |) -> skipn n (xs ++ ys) = ys.
Proof. intros ->. now rewrite List.skipn_app, skipn_all, Nat.sub_diag. Qed.

Lemma skipn_app_app {X : Type} (l1 l2 l3 : list X) : skipn (length (l1 ++ l2)) (l1 ++ l3) = skipn (length l2) l3.
Proof.
  rewrite skipn_app, length_app, skipn_all2 by lia.
  cbn. f_equal. lia.
Qed.

Lemma vec_app_spec {X n m} (v : Vector.t X n) (w : Vector.t X m) :
  vec_app v w = Vector.append v w.
Proof.
  induction v.
  - cbn. eapply vec_pos_ext. intros. now rewrite vec_pos_set.
  - rewrite vec_app_cons. cbn. congruence.
Qed.

Lemma Vector_map_app {X Y k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) (f : X -> Y) :
  Vector.map f (Vector.append v1 v2)%vector = Vector.append (Vector.map f v1) (Vector.map f v2).
Proof.
  induction v1; cbn; congruence.
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
  destruct (Vector.splitat n v) as [t t0] eqn:E.
  eexists (vec_head t0, t).
  erewrite <- Vector.append_splitat; [now rewrite cast_eq_refl|].
  rewrite E. f_equal. eapply (Vector.caseS' t0). cbn.
  intros ?. now eapply Vector.case0.
Qed.

Lemma nth_error_vec_list {X n} (v : Vector.t X n) m (H : m < n) x :
  nth_error (vec_list v) m = Some x ->
  vec_pos v (Fin.of_nat_lt H) = x.
Proof.
  induction v as [| ??? IHv] in m, H |- *; cbn; [lia|].
  destruct m; cbn; [congruence | now apply IHv].
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
  induction l1 as [|?? IHl1] in i |- *; cbn; [now rewrite Nat.sub_0_r |].
  intros Hi. destruct i; [lia|].
  cbn. rewrite IHl1; [reflexivity| lia].
Qed.

Lemma update_app_left {X} (x : X) l1 l2 i : 
  i < length l1 ->
  update i (l1 ++ l2) x = update i l1 x ++ l2.
Proof.
  induction l1 as [|?? IHl1] in i |- *; cbn; [lia|].
  intros Hi. destruct i; cbn; [reflexivity|].
  rewrite IHl1; [reflexivity|lia].
Qed.

Lemma vec_list_vec_change {X n} (v : Vector.t X n) (x : X) (p : pos n) :
  vec_list (vec_change v p x) = update (proj1_sig (Fin.to_nat p)) (vec_list v) x.
Proof.
  induction v as [|??? IHv]; cbn.
  - inversion p.
  - eapply (Fin.caseS' p); cbn; [reflexivity|].
    intros p0. specialize (IHv p0). destruct (Fin.to_nat p0) eqn:E. cbn in *. now f_equal.
Qed.

Lemma vec_change_app_right {X} (n m : nat) v1 v2 p x:
  vec_change (@vec_app X n m v1 v2) (pos_right n p) x = vec_app v1 (vec_change v2 p x).
Proof.
  induction v1 as [| ??? IHv1].
  - rewrite !vec_app_nil. reflexivity.
  - rewrite !vec_app_cons. cbn. now rewrite IHv1.
Qed.

Lemma pos_right_left {n m} p q : @pos_left n m p <> @pos_right n m q.
Proof.
  induction n; cbn.
  - inversion p.
  - eapply (Fin.caseS' p).
    + cbn. congruence.
    + cbn. intros ? ? % pos_nxt_inj. firstorder.
Qed.

Lemma pos_left_right {n m} p q : @pos_right n m q <> @pos_left n m p.
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
  - intros p0. rewrite !vec_pos_app_left.
    destruct (pos_eq_dec p p0).
    + subst. rewrite vec_change_eq; [|reflexivity]. now rewrite vec_change_eq.
    + rewrite vec_change_neq; [|intros ? % pos_left_inj; congruence].
      rewrite vec_pos_app_left. rewrite vec_change_neq; auto.
  - intros p0. rewrite !vec_pos_app_right. rewrite vec_change_neq; auto. now rewrite vec_pos_app_right.
Qed.

Lemma vec_app_inj {X} (n m : nat) v1 v2 v2' :
  @vec_app X n m v1 v2 = vec_app v1 v2' -> v2 = v2'.
Proof.
  induction v1 as [| ??? IHv1].
  - now rewrite !vec_app_nil.
  - rewrite !vec_app_cons. intros H. eapply IHv1.
    now eapply (f_equal (@vec_tail _ _)) in H.
Qed.

Lemma vec_pos_spec {k} {X} (p : pos k) (v : Vector.t X k) : vec_pos v p = Vector.nth v p.
Proof.
  induction v in p |- *.
  - inversion p.
  - eapply (Fin.caseS' p).
    + reflexivity.
    + intros. cbn. eauto.
Qed.

Lemma pos_right_inj {n m} p q :
  @pos_right n m p = @pos_right n m q -> p = q.
Proof.
  induction n as [|n IHn] in p, q |- *; cbn in *.
  - eauto.
  - intros H. eapply IHn, pos_nxt_inj, H.
Qed.

Lemma vec_pos_const {k} {X x} (p : pos k) : vec_pos (@Vector.const X x k) p = x.
Proof.
  induction p; cbn; eauto.
Qed.

Lemma vec_map_spec {X Y n} (v : Vector.t X n) (f : X -> Y) :
  vec_map f v = Vector.map f v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma pos_left_inj {n m} p q :
  @pos_left n m p = @pos_left n m q -> p = q.
Proof.
  induction p as [| ? ? IHp] in q |- *; cbn in *.
  - eapply (Fin.caseS' q).
    + reflexivity.
    + clear q. cbn. congruence.
  - eapply (Fin.caseS' q).
    + cbn. congruence.
    + clear q. cbn. intros. f_equal. eapply IHp.
      now eapply pos_nxt_inj.
Qed.

(* Utility lemmas for BSM instructions*)
Lemma POP_true_spec m (STACK : Fin.t m) n t j v v' k1 k2 :
  vec_pos v STACK = true :: v' ->
  bsm_sss (POP STACK k1 k2) (j, v) (n, t) ->
  n = j + 1 /\ t = vec_change v STACK v'.
Proof.
  intros H H0.
  inversion H0 as [????? H1|?????? H1 | ?????? H1 | ]; subst; try clear H0; 
  rewrite H1 in H; [inversion H | inversion H |].
  injection H. clear H. intros H. subst. split; [lia | reflexivity].
Qed.

Lemma POP_false_spec m (STACK : Fin.t m) n t j v v' k1 k2 :
  vec_pos v STACK = false :: v' ->
  bsm_sss (POP STACK k1 k2) (j, v) (n, t) ->
  n = k1 /\ t = vec_change v STACK v'.
Proof.
  intros H H0.
  inversion H0 as [????? H1|?????? H1 | ?????? H1 | ]; subst; try clear H0; rewrite H1 in H; [inversion H |  | inversion H].
  injection H. clear H. intros H. subst. split; [lia | reflexivity].
Qed.

Lemma POP_empty_spec m (STACK : Fin.t m) n t j v k1 k2 :
  vec_pos v STACK = [] ->
  bsm_sss (POP STACK k1 k2) (j, v) (n, t) ->
  n = k2 /\ v = t.
Proof.
  intros H H0.
  inversion H0 as [????? H1|?????? H1 | ?????? H1 | ]; subst; try clear H0; rewrite H1 in H; [| inversion H | inversion H].
  now split.
Qed.

Lemma POP_empty_spec' m (STACK1 STACK2 : Fin.t m) n t j v k1 k2 :
  vec_pos v STACK1 = [] ->
  bsm_sss (POP STACK2 k1 k2) (j, v) (n, t) ->
  vec_pos t STACK1 = [].
Proof.
  intros H0 H1.
  destruct (vec_pos v STACK2) as [| b l] eqn:E.
  - apply POP_empty_spec in H1; [| apply E].
    destruct H1 as [H1 ?]. subst. apply H0.
  - destruct b; [apply POP_true_spec with (v' := l) in H1; [| apply E]| apply POP_false_spec with (v' := l) in H1; [| apply E]].
    all: destruct H1; subst; rewrite vec_change_neq; [apply H0|];
    assert (NEQ : STACK2 <> STACK1); [| apply NEQ];
    unfold "<>"; intros H3; rewrite <- H3 in H0; rewrite E in H0; inversion H0.
Qed.

Lemma PUSH_spec (STACK : Fin.t 5) n t j v b :
  bsm_sss (PUSH STACK b) (j, v) (n, t) ->
  n = j + 1 /\ t = vec_change v STACK (b :: (vec_pos v STACK)).
Proof.
  intros H0.
  inv H0.
  now split; [lia | reflexivity].
Qed.

(* Utility function and lemmas for truncation*)
Fixpoint remove_leading_falses (l : list bool) :=
  match l with
  | false :: l' => remove_leading_falses l'
  | l' => l'
  end.

Lemma rev_forallb (A : Type) P (l : list A):
  forallb P (rev l) =  forallb P l.
Proof. 
  induction l as [| a l IHl]; [reflexivity|].
  cbn.
  rewrite forallb_app, IHl.
  cbn.
  now rewrite andb_true_r, andb_comm.
Qed.

Lemma leading_false_spec v1 : exists n, (exists l, v1 = repeat false n ++ true :: l) \/ v1 = repeat false n.
Proof.
  induction v1 as [| a l IHv1]; [exists 0; now right |].
  destruct IHv1 as [n [IHv1 | IHv1]]; [destruct IHv1 as [l' IHv1]|]; subst.
  - destruct a; [exists 0 | exists (S n)]; left; eexists _; now reflexivity.
  - destruct a.
      + exists 0. left. eexists _. now reflexivity.
      + exists (S n). right. now reflexivity.
Qed.

Lemma remove_leading_falses_spec_false_only n :
  remove_leading_falses (repeat false n) = [].
Proof.
  induction n as [| ? IHn]; [reflexivity | apply IHn].
Qed.

Lemma remove_leading_falses_dist (l l1 :list bool) : 
  remove_leading_falses (l ++ true :: l1) = remove_leading_falses l ++ true :: l1.
Proof.
  induction l as [| a ? IHl]; [reflexivity|].
  destruct a; [reflexivity| apply IHl].
Qed.

Lemma remove_leading_falses_spec l n :
  remove_leading_falses (repeat false n ++ true :: l) = true :: l.
Proof.
  now rewrite remove_leading_falses_dist, remove_leading_falses_spec_false_only.
Qed.

Lemma true_not_repeat_false x x0 :
  forallb negb (repeat false x ++ true :: x0) = false.
Proof.
  rewrite forallb_app.
  now destruct (forallb negb (repeat false x)).
Qed.

Lemma repeat_forallb n :
  forallb negb (repeat false n) = true.
Proof.
  induction n as [| ? IHn]; [reflexivity|cbn; apply IHn].
Qed.

(* A single instruction from a program is a subprogram of the full program *)
Lemma sc_spec n i j (P : list (bsm_instr n)) x :
  in_code j (i, P) ->
  nth_error P (j - i) = Some x ->
  (j, [x]) <sc (i, P).
Proof.
  intros H1 H2.
  eexists (firstn (j - i) P), (skipn (j - i + 1) P).
  split.
  - cbn. 
    replace (j - i + 1) with (S (j - i)) by lia.
    now rewrite firstn_skipn_middle.
  - cbn in H1.
    rewrite firstn_length_le; [|lia].
    rewrite Nat.add_sub_assoc; [|lia].
    now rewrite Nat.add_comm, Nat.add_sub.
Qed.

(* BSM cast definition and lemmas *)
Definition BSM_cast {n} (P : list (bsm_instr n)) {m} (E : n = m) : list (bsm_instr m).
Proof. subst m. exact P. Defined.

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


(* ---SBTM Simulation--- *)

Definition complete_encode (Σ : finType) n (t : Vector.t (tape Σ) n) : SBTMNotations.tape:=
  HaltTM_1_to_SBTM_HALT.encode_tape ((encode_tape' (Vector.nth (mTM_to_TM.enc_tape [] t) Fin0))).

Lemma SBTM_complete_simulation n Σ (M : TM Σ n) :
  {M' : SBTM &
     {q_start : SBTMNotations.state M' |
        (forall q t t' t'', TM.eval M (TM.start M) t q t' -> 
          SBTM_facts.almost_eq_tape t'' (complete_encode t) ->
        (exists k q' t''', SBTM.steps M' k (q_start, t'') = Some (q', t''') /\
        SBTM.steps M' (S k) (q_start, t'') = None /\
        SBTM_facts.almost_eq_tape t''' (complete_encode t'))) /\
        (forall t, (exists k , SBTM.steps M' k (q_start, complete_encode t) = None) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}}.
Proof.
  destruct (TM_sTM_simulation M) as (M1 & Hf1 & Hb1).
  destruct (binary_simulation M1) as (M2 & Hf2 & Hb2).
  destruct (SBTM_simulation M2) as [M3 [q_start [Hf3 Hb3]]].
  eexists M3, q_start.
  split.
  - intros q t t' t'' H H0.
    destruct (Hf1 _ _ _ H) as [q' H1].
    destruct (Hf2 _ _ _ H1) as [q'' H2].
    apply (Hf3 _ _ _ t'' H2 H0).
  - clear Hf1 Hf2 Hf3.
    intros t H.
    apply Hb1.
    apply Hb2.
    apply Hb3.
    apply H.
Qed.


(* ---Extend BSM--- *)

(* Lift instructions to more stacks *)
Definition bsm_addstracks' n m (P : bsm_instr n) : (bsm_instr (m + n)) :=
  (fun x => match x with
  | bsm_pop x c1 c2 => bsm_pop (pos_right m x) c1 c2
  | bsm_push x b => bsm_push (pos_right m x) b end) P.

Definition bsm_addstacks n m (P : list (bsm_instr n)) : list (bsm_instr (m + n)):=
map (@bsm_addstracks' n m) P.

(* Lift single step *)
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
  eexists. eexists. eexists. eexists. eexists. split.  1: reflexivity. split.  1: rewrite length_map.  1: reflexivity.
  now apply BSM_addstacks_step.
Qed.

Lemma BSM_addstacks_step_bwd' n i (P : list (bsm_instr n)) m j v v'' out :
  sss_step (bsm_sss (n := m + n)) (i, (@bsm_addstacks n m P)) (j, vec_app v'' v) out -> exists o v', out = (o, vec_app v'' v') /\ sss_step (bsm_sss (n := n)) (i, P) (j, v) (o, v').
Proof.
  intros (? & ? & ? & ? & ? & ? & ? & ?). inv H. inv H0.
  assert (nth_error (bsm_addstacks m P) (length x0) = Some x1).  1: rewrite H4.  1: rewrite nth_error_app2. 2:lia.  1: rewrite Nat.sub_diag.  1: reflexivity.
  unfold bsm_addstacks in H.
  destruct (nth_error_Some P (|x0|)) as [_ HH].
  destruct (nth_error P (|x0|)) as [d | ] eqn:E. 2:{ exfalso. eapply HH; try reflexivity. erewrite <- (length_map _ P). unfold bsm_addstacks in H4. rewrite H4.
  rewrite length_app. cbn. lia. }
  pose proof (E' := E).
  eapply map_nth_error in E. unfold bsm_addstacks in H4. rewrite H4 in E.
  rewrite nth_error_app2 in E. 2:lia. rewrite Nat.sub_diag in E. cbn in E. inv E.
  eapply BSM_addstacks_step_bwd in H1 as (? & ? & ? & ?). subst.
  repeat eexists; eauto.
  1: f_equal.  1: instantiate (2 := firstn (length x0) P).
  1: instantiate (1 := skipn (1 + length x0) P).
  2:{ f_equal. rewrite length_firstn. enough (|x0| < |P|).  1: lia.
      eapply nth_error_Some. now rewrite E'. }
  rewrite <- (firstn_skipn (length x0) P) at 1.
  f_equal.
  clear - H4. induction x0 in P, H4 |- *.
  - cbn in *. destruct P; inv H4. destruct b, d; inv H0; eapply pos_right_inj in H1; subst; reflexivity.
  - destruct P; cbn in *; inv H4. now rewrite IHx0.
Qed.

(* Use sss_compute instead of sss_steps *)
Lemma BSM_addstacks' n i (P : list (bsm_instr n)) m j v o v' v'' :
  sss_compute (bsm_sss (n := n)) (i, P) (j, v) (o, v') -> sss_compute (bsm_sss (n := m + n)) (i, (@bsm_addstacks n m P)) (j, vec_app v'' v) (o, vec_app v'' v').
Proof.
  intros H.
  destruct H as [k H].
  revert j v v' v'' o H.
  induction k as[| k IHk]; intros j v v' v'' o H.
  - exists 0. apply sss_steps_0_inv in H. injection H. intros. subst. clear H.
    now apply sss_steps_0.
  - apply sss_steps_S_inv' in H.
    destruct H as [[s1 s2] [H1 H2]].
    destruct (IHk _ _ _ v'' _ H2) as [k' IHk'].
    exists (S k').
    eapply in_sss_steps_S; [apply (BSM_addstacks_step' v'' H1) | apply IHk'].
Qed.


Lemma BSM_addstacks_bwd' n i (P : list (bsm_instr n)) m j v v'' out :
  sss_compute (bsm_sss (n := m + n)) (i, (@bsm_addstacks n m P)) (j, vec_app v'' v) out -> exists o v', out = (o, vec_app v'' v') /\ sss_compute (bsm_sss (n := n)) (i, P) (j, v) (o, v').
Proof.
  intros [k H].
  revert j v v'' out H.
  induction k as [|k IHk]; intros j v v'' out H.
  - apply sss_steps_0_inv in H.
    eexists _ ,_.
    split; [now rewrite H |].
    exists 0. now apply sss_steps_0.
  - apply sss_steps_S_inv' in H.
    destruct H as [st2 [H1 H2]].
    destruct (BSM_addstacks_step_bwd' H1) as [o [v' [H3 H4]]].
    rewrite H3 in H1, H2.
    destruct (IHk _ _ _ _ H2) as [o' [v''' [IHk1 [k' IHk2]]]].
    eexists _, _.
    split; [apply IHk1 |].
    exists (S k').
    apply (in_sss_steps_S H4 IHk2).
Qed.


Lemma BSM_addstacks n i (P : list (bsm_instr n)) m :
   {P' | length P = length P' /\ (forall j v o v', BSM.eval n (i, P) (j, v) (o, v') -> forall v'', BSM.eval (m + n) (i, P') (j, Vector.append v'' v) (o, Vector.append v'' v'))
          /\ forall v v'' j out, BSM.eval (m + n) (i, P') (j, Vector.append v'' v) out -> exists out, BSM.eval n (i, P) (j, v) out}.
Proof.
  exists (bsm_addstacks m P). split. { unfold bsm_addstacks. now rewrite length_map. }
  setoid_rewrite eval_iff.
  split.
  - intros j v o v' [H1 H2] v''. split. 2:{ cbn. unfold bsm_addstacks. rewrite length_map. exact H2. }
    rewrite <- !vec_app_spec. now eapply BSM_addstacks'.
  - intros v v'' j [o1 o2] H. eapply eval_iff in H as [H1 H2].
    rewrite <- vec_app_spec in H1.
    eapply BSM_addstacks_bwd' in H1 as (? & ? & ? & ?). inv H.
    eexists (_, _). eapply eval_iff. split; [apply H0 |].
    cbn in *. unfold bsm_addstacks in H2. rewrite length_map in H2. exact H2.
Qed.


(* Lifting a program does not change length *)
Lemma bsm_length m n (P : list (bsm_instr n)):
  length (bsm_addstacks m P) = length P.
Proof.
    destruct P as [| ? P]; [reflexivity |].
    cbn.
    now rewrite length_map.
Qed.

(* ---BSM encoding--- *)

(* Encode tape vector on 5 BSM stacks.
   0: Truncation stack
   1: left of the current symbol
   2: current symbol
   3: right of the current symbol
   5: Unconditional jump stack
 *)
Definition encode_bsm (Σ : finType) n (t : Vector.t (tape Σ) n) :=
let t' := (SBTM_facts.truncate_tape (complete_encode t)) in 
let t'' := (SBTM_HALT_to_HaltBSM.encode_tape t') in
  vec_app [|[]|] t''.


Arguments encode_bsm {_ _} _, _ {_} _.

Arguments encode_tapes : simpl never.

(* encode_symbol produces lists of length 2*)
Lemma encode_length  l : (| flat_map encode_symbol l |) = 2 * (| l |).
Proof.
  induction l; [reflexivity| ].
  cbn in *.
  lia.
Qed.

(* flat_map encode_symbol ends on true or is empty*)
Lemma encode_symbol_spec l1 :
  (exists l2, flat_map encode_symbol l1 = l2 ++ [true]) \/ l1 = [].
Proof.
  induction l1 as [ | a l1 IHl1].
  - right. reflexivity.
  - destruct IHl1 as [[l2 IHl1] | IHl1]; left.
    + exists (a :: true :: l2).
      cbn in *.
      now rewrite IHl1.
    + exists [a].
      now rewrite IHl1.
Qed.

(* Reverse, remove false prefix, reverse does the same as truncate function*)
Lemma trunc_spec l:
  rev (remove_leading_falses (rev l)) = SBTM_facts.truncate l.
Proof.
  induction l as [| a l IHl]; [ now reflexivity |].
  destruct a; cbn; [now rewrite <- IHl, remove_leading_falses_dist, rev_unit |].
  destruct (leading_false_spec (rev l)) as [x [[x0 H] | H]].
  - rewrite H in IHl.
    rewrite H, <- app_assoc, <- app_comm_cons, remove_leading_falses_dist, <- IHl.
    assert (E := true_not_repeat_false x x0).
    rewrite <- rev_forallb in E.
    rewrite <- H, rev_involutive in E.
    now rewrite E, remove_leading_falses_dist, <- rev_unit, <- app_assoc, app_comm_cons.
  - rewrite H, <- repeat_cons, <- IHl.
    assert (H1 := repeat_forallb x).
    rewrite <- H, rev_forallb in H1.
    rewrite H1.
    simpl.
    now rewrite remove_leading_falses_spec_false_only.
Qed.
        
(* Truncate does not have an effect because encode_symbol always ends on true*)
Lemma truncate_irrel l:
  SBTM_facts.truncate (flat_map encode_symbol l) = flat_map encode_symbol l.
Proof.
  destruct (encode_symbol_spec l) as [[l2 H] | H]; [| now rewrite H].
  rewrite H, <- trunc_spec, rev_unit.
  simpl.
  now rewrite rev_involutive.
Qed.

(* truncate_irrel applied to an encoded BSM stack configuration *)
Lemma truncate_irrel_encoding (Σ : finType) n (t: vec (tape Σ) n) :
  (encode_bsm t)@[Fin3] = (vec_app [|[]|] (SBTM_HALT_to_HaltBSM.encode_tape (complete_encode t)))@[Fin3].
Proof.
  unfold encode_bsm.
  simpl.
  now rewrite truncate_irrel.
Qed.

Lemma encode_bsm_nil (Σ : finType) n   :
  { '(str2, n') | forall (t : Vector.t (tape Σ) n), (encode_bsm Σ (niltape ::: t))@[Fin3] =  str2 ++ (skipn n' ((encode_bsm Σ t)@[Fin3]))}.
Proof.
  eexists (flat_map encode_symbol (encode_sym _ ++ true :: false :: encode_sym _ ++ true :: false :: encode_sym _), _). intros t.
  cbn.
  set (s := encode_sym _).
  set (f := map _).
  rewrite !truncate_irrel.
  rewrite !flat_map_app.
  rewrite skipn_app'; [|subst s; now rewrite encode_length, length_encode_sym]. 
  rewrite <- !flat_map_app. 
  apply f_equal.
  assert ( Hreorder : forall l1 l2 l3 l4,
  l1 ++ true :: false :: l2 ++ true :: false :: l3 ++ true :: l4 =
  (l1 ++ true :: false :: l2 ++ true :: false :: l3) ++ true :: l4). 
  { intros. now repeat (rewrite <- app_assoc; cbn). }
  apply Hreorder.
Qed.

Definition strpush_common_short (Σ : finType) (s b : Σ) :=
flat_map encode_symbol(
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
                       (inr (sigList_X (EncodeTapes.MarkedSymbol b))))).


Definition strpush_common (Σ : finType) (s b : Σ) :=
strpush_common_short s b ++
            flat_map encode_symbol(
                  true
                  :: false :: nil).


Definition strpush_zero (Σ : finType) (s b : Σ) :=
  strpush_common s b ++
  flat_map encode_symbol(
                      encode_sym
                          (projT1
                             (projT2
                                (FinTypes.finite_n
                                   (finType_CS
                                      (boundary +
                                       sigList (EncodeTapes.sigTape Σ)))))
                             (inr (sigList_X (EncodeTapes.RightBlank false))))).


Lemma encode_bsm_at0 (Σ : finType) n (t : Vector.t (tape Σ) n) :
   (encode_bsm Σ t) @[Fin0] = [].
Proof. reflexivity. Qed.

Lemma encode_bsm_at1 (Σ : finType) n (t : Vector.t (tape Σ) n) :
   (encode_bsm Σ t) @[Fin1] = [].
Proof. reflexivity. Qed.

Lemma encode_bsm_at2 (Σ : finType) n :
   forall (t : Vector.t (tape Σ) n), (encode_bsm Σ t) @[Fin2] = [true].
Proof. reflexivity. Qed.

Lemma encode_bsm_at4 (Σ : finType) n (t : Vector.t (tape Σ) n) :
   (encode_bsm Σ t) @[Fin4] = [].
Proof. reflexivity. Qed.

Lemma encode_bsm_zero (Σ : finType) s b :
  { n' | forall n(t : Vector.t (tape Σ) n), (encode_bsm Σ (encNatTM s b 0 ::: t)) @[Fin3] = strpush_zero s b ++ (skipn n' ((encode_bsm Σ t)@[Fin3]))}.
Proof.
  eexists _. intros ? t. cbn.
  rewrite !truncate_irrel, !flat_map_app.
  rewrite skipn_app'; [ | now rewrite encode_length, length_encode_sym].
  unfold strpush_zero, strpush_common, strpush_common_short.
  assert (Hreorder : forall l1 l2 l3 l4 l5 l6,
    l1 ++ true :: false :: l2 ++ true :: false :: l3 ++ true :: false :: l4 ++ true :: false :: l5 ++ true :: l6 =
    (((l1 ++ true :: false :: l2 ++ true :: false :: l3 ++ true :: false :: l4) ++ [true; false]) ++ l5) ++ true :: l6).
  { intros. now repeat (rewrite <- app_assoc; cbn). }
  rewrite <- !flat_map_app.
  apply f_equal.
  apply Hreorder.
Qed.

Definition strpush_succ (Σ : finType) (s b : Σ) :=
strpush_common s b ++
flat_map encode_symbol (
                     encode_sym
                          (projT1
                             (projT2
                                (FinTypes.finite_n
                                   (finType_CS
                                      (boundary +
                                       sigList (EncodeTapes.sigTape Σ)))))
                             (inr (sigList_X (EncodeTapes.UnmarkedSymbol s))))).

Lemma encode_tapes_cons {sig n} t (ts : tapes sig n) : encode_tapes (t ::: ts) = sigList_cons :: map sigList_X (encode_tape t) ++ encode_tapes ts.
Proof. reflexivity. Qed.

Lemma encode_bsm_succ (Σ : finType) n m s b (t : Vector.t (tape Σ) n) :
      (encode_bsm Σ (encNatTM s b (S m) ::: t)) @[Fin3] = strpush_succ s b ++ (skipn (length (strpush_common_short s b)) ((encode_bsm Σ (encNatTM s b m ::: t))@[Fin3])).
Proof.
  rewrite !truncate_irrel_encoding.
  rewrite <- !vec_pos_spec.
  rewrite !vec_pos_app_right.
  cbn.
  rewrite (encode_tapes_cons (encNatTM s b m)). cbn.
  assert (Happ_assoc : forall l1 l2 l3 l4 l5,
    l1 ++ true :: false :: l2 ++ true :: false :: l3 ++ true :: false :: l4 ++ true :: l5 =
    (l1 ++ true :: false :: l2 ++ true :: false :: l3 ++ true :: false :: l4) ++ true :: l5).
  { intros. now repeat (rewrite <- app_assoc; cbn). }
  rewrite Happ_assoc.
  rewrite !flat_map_app.
  rewrite skipn_app'.
  - unfold strpush_succ, strpush_common, strpush_common_short.
    rewrite <- !flat_map_app.
    apply f_equal.
    assert( Hreorder : forall l1 l2 l3 l4 l5 l6,
    l1 ++ true :: false :: l2 ++ true :: false :: l3 ++ true :: false :: l4 ++ true :: false :: l5 ++ true :: l6 =
    (((l1 ++ true :: false :: l2 ++ true :: false :: l3 ++ true :: false :: l4) ++ [true; false]) ++ l5) ++ true :: l6). {
   intros. now repeat (rewrite <- app_assoc; cbn). }
    apply Hreorder.
  - rewrite length_app.
    rewrite encode_length.
    rewrite length_encode_sym.
    unfold strpush_common_short.
    rewrite flat_map_app.
    rewrite length_app.
    rewrite encode_length.
    now rewrite length_encode_sym.
Qed.


(* ---Truncation simulation--- *)

Section Truncation_Construction.

  (* STACK is the stack to perform truncation on. STACK is different from the truncation and the empty stack. *)
  Context (i : nat) (STACK : Fin.t 5) (STACK_NEQ_FIN4 : STACK <> Fin4) (STACK_NEQ_FIN0 : STACK <> Fin0).

  Definition TRUNC_length := 12.
  Definition END := i + TRUNC_length.

  (* Performs truncation on one stack *)
  #[local] Definition TRUNC : list (bsm_instr 5) :=
    let JMP := fun i => POP Fin4 i i in
    (* i + 0 *) POP STACK (i + 3) (i + 5) ::
    (* i + 1 *) PUSH Fin0 true ::
    (* i + 2 *) JMP (i + 0) ::
    (* i + 3 *) PUSH Fin0 false ::
    (* i + 4 *) JMP (i + 0) ::

    (* i + 5 *) POP Fin0 (i + 5) END ::
    (* i + 6 *) PUSH Fin0 true ::

    (* i + 7 *) POP Fin0 (i + 10) END ::
    (* i + 8 *) PUSH STACK true ::
    (* i + 9 *) JMP (i + 7) ::
    (* i + 10 *) PUSH STACK false ::
    (* i + 11 *) JMP (i + 7) :: [].


  (* Specifies one traversal of the first loop (i to (i + 4))*)
  #[local] Lemma Truncation_first_loop_single a v v1:
    vec_pos v Fin4 = [] ->
    vec_pos v STACK = a :: v1 ->
    (i, TRUNC) // (i, v) ->> 
    (i, vec_change (vec_change v STACK v1) Fin0 (a :: vec_pos v Fin0)).
  Proof using STACK_NEQ_FIN0 STACK_NEQ_FIN4.
    unfold TRUNC.
    intros H1 H2.
    destruct a.
    - bsm sss POP one with STACK (i + 3) (i + 5) v1.
      bsm sss PUSH with Fin0 true.
      bsm sss POP empty with Fin4 (i + 0) (i + 0).
      + repeat rewrite vec_change_neq; easy.
      + rewrite Nat.add_0_r.
        bsm sss stop.
        rewrite vec_change_neq; easy.
    - bsm sss POP zero with STACK (i + 3) (i + 5) v1.
      bsm sss PUSH with Fin0 false.
      replace (1 + ( i + 3)) with (i + 4) by lia.
      bsm sss POP empty with Fin4 (i + 0) (i + 0).
      + apply sc_spec; cbn; [lia |now replace (i + 4 - i) with 4 by lia].
      + repeat rewrite vec_change_neq; easy.
      + rewrite Nat.add_0_r.
        bsm sss stop.
        rewrite vec_change_neq; easy.
  Qed.

  (* Specifies traversal of the first loop (i to (i + 4))*)
  #[local] Lemma Truncation_first_loop v v0 v1:
    vec_pos v Fin4 = [] ->
    vec_pos v Fin0 = v0 ->
    vec_pos v STACK = v1 ->
    (i, TRUNC) // (i, v) ->> (i, 
    vec_change (vec_change v STACK []) Fin0 (rev v1 ++ v0)).
  Proof using STACK_NEQ_FIN0 STACK_NEQ_FIN4.
    revert v0 v.
    induction v1 as [|a v1 IHv1]; intros v2 v H1 H2 H3.
    - simpl. exists 0. rewrite <- H3. rewrite vec_change_same. rewrite <- H2. rewrite vec_change_same. constructor.
    - eapply sss_compute_trans.
      + apply Truncation_first_loop_single; [easy | now apply H3].
      + enough (E :(vec_change (vec_change (vec_change (vec_change v STACK v1) Fin0 (a :: vec_pos v Fin0)) STACK []) Fin0(rev v1 ++ a :: v2)) = (vec_change (vec_change v STACK []) Fin0 (rev (a :: v1) ++ v2))).
        * rewrite <- E, <- H2.
          apply IHv1; now autorewrite with vec_simpl.
        * rewrite <- H2.
          rewrite vec_change_comm; [|easy].
          rewrite vec_change_idem.
          rewrite vec_change_comm; [|easy].
          rewrite vec_change_idem.
          simpl.
          rewrite <- app_assoc.
          now rewrite <- app_comm_cons.
  Qed.

  (* Specifies traversal from first to second loop (i to (i + 5))*)
  #[local] Lemma Truncation_first_to_second v:
    vec_pos v Fin4 = [] ->
    vec_pos v STACK = [] ->
    (i, TRUNC) // (i, v) ->> (i + 5, v).
  Proof.
    unfold TRUNC.
    intros H1 H2.
    bsm sss POP empty with STACK (i + 3) (i + 5).
    bsm sss stop.
  Qed.

  (* Specifies traversal of second loop ((i + 5) and (i + 6)) if STACK contains a false prefix *)
  #[local] Lemma Truncation_second_loop_repeat_false n v v0:
    vec_pos v Fin4 = [] ->
    vec_pos v Fin0 = (repeat false n) ++ v0 ->
    vec_pos v STACK = [] ->
    (i, TRUNC) // (i + 5, v) ->> (i + 5, vec_change v Fin0 v0).
  Proof using STACK_NEQ_FIN0.
    revert v.
    induction n as [|n IHn]; intros v H0 H1 H2.
    - exists 0. cbn in H1. rewrite <- H1. rewrite vec_change_same. constructor.
    - eapply sss_compute_trans.
      + unfold TRUNC.
        bsm sss POP zero with Fin0 (i + 5) (END) (repeat false n ++ v0).
        bsm sss stop.
      + enough (H :vec_change (vec_change v Fin0 (repeat false n ++ v0)) Fin0 v0 = vec_change v Fin0 v0).
        * rewrite <- H.
          apply IHn; now autorewrite with vec_simpl.
        * now rewrite vec_change_idem.
  Qed.

  (* Specifies traversal of second loop ((i + 5) and (i + 6)) if STACK starts with true *)
  #[local] Lemma Truncation_second_loop_true v v0:
    vec_pos v Fin4 = [] ->
    vec_pos v Fin0 = true :: v0 ->
    vec_pos v STACK = [] -> 
    (i, TRUNC) // (i + 5, v) ->> (i + 7, v).
  Proof using STACK_NEQ_FIN0 STACK_NEQ_FIN4.
    unfold TRUNC.
    intros H H0 H1.
    bsm sss POP one with Fin0 (i + 5) (END) v0.
    bsm sss PUSH with Fin0 true.
    - apply sc_spec; [cbn; lia| now replace (1 + (i + 5) - i) with 6 by lia].
    - bsm sss stop.
      f_equal; [lia|].
      rewrite vec_change_idem.
      rewrite vec_change_eq; [|easy].
      rewrite <- H0.
      now rewrite vec_change_same.
  Qed.

  (* Specifies traversal of second loop ((i + 5) and (i + 6)) if STACK is empty *)
  #[local] Lemma Truncation_second_loop_empty v:
    vec_pos v Fin0 = [] ->
    vec_pos v STACK = [] ->
    vec_pos v Fin4 = [] ->
    (i, TRUNC) // (i + 5, v) ->> (END, v).
  Proof.
    unfold TRUNC.
    intros H H0 H1.
    bsm sss POP empty with Fin0 (i + 5) (END).
    bsm sss stop.
  Qed.

  (* Specifies one traversal of third loop ((i + 7) to (i + 11)) *)
  #[local] Lemma Truncation_third_loop_single a v v0:
    vec_pos v Fin0 = a :: v0 ->
    vec_pos v Fin4 = [] ->
    (i, TRUNC) // (i + 7, v) ->> (i + 7, vec_change (vec_change v Fin0 v0) STACK (a :: vec_pos v STACK)).
  Proof using STACK_NEQ_FIN0 STACK_NEQ_FIN4.
    unfold TRUNC.
    intros H H0.
    destruct a.
    - bsm sss POP one with Fin0 (i + 10) (END) v0.
      bsm sss PUSH with STACK true.
      bsm sss POP empty with Fin4 (i + 7) (i + 7); [now autorewrite with vec_simpl|].
      bsm sss stop.
      now autorewrite with vec_simpl.
    - bsm sss POP zero with Fin0 (i + 10) (END) v0.
      bsm sss PUSH with STACK false.
      bsm sss POP empty with Fin4 (i + 7) (i + 7); [| now autorewrite with vec_simpl |].
      + apply sc_spec; [cbn; lia | now replace (1 + (i + 10) - i) with 11 by lia].
      + bsm sss stop.
        now autorewrite with vec_simpl.
  Qed.

  (* Specifies traversal of third loop ((i + 7) to (i + 11)) *)
  #[local] Lemma Truncation_third_loop v v0 v1:
    vec_pos v Fin4 = [] ->
    vec_pos v Fin0 = v0 ->
    vec_pos v STACK = v1 ->
    (i, TRUNC) // (i + 7, v) ->> (i + 7,
    vec_change (vec_change v STACK (rev v0 ++ v1)) Fin0 []).
  Proof using STACK_NEQ_FIN0 STACK_NEQ_FIN4.
    revert v v1.
    induction v0 as [|a v0 IHv0].
    - intros v l H0 H1 H2. cbn. exists 0. rewrite <- H2, vec_change_same, <- H1, vec_change_same. now constructor.
    - intros v l H0 H1 H2.
      eapply sss_compute_trans.
      + apply Truncation_third_loop_single; [|easy].
        now apply H1.
      + enough (H :vec_change (vec_change (vec_change (vec_change v Fin0 v0) STACK
  (a :: vec_pos v STACK)) STACK (rev v0 ++ a :: l))
  Fin0 [] = vec_change (vec_change v STACK (rev (a :: v0) ++ l))
  Fin0 []).
      * rewrite <- H, H2.
        apply IHv0; now autorewrite with vec_simpl; easy.
      * rewrite vec_change_idem.
        rewrite vec_change_comm; [|easy].
        rewrite vec_change_idem.
        rewrite vec_change_comm; [|easy].
        simpl.
        now rewrite <- app_assoc.
  Qed.

  (* Specifies traversal from (i + 7) to END*)
  #[local] Lemma Truncation_spec_final v:
    vec_pos v Fin4 = [] ->
    vec_pos v Fin0 = [] ->
    (i, TRUNC) // (i + 7, v) ->> (END, v).
  Proof.
    unfold END, TRUNC, TRUNC_length.
    intros H H0.
    bsm sss POP empty with Fin0 (i + 10) (i + 12); [|bsm sss stop].
    apply sc_spec; [cbn; lia |  now replace (i + 7 - i) with 7 by lia].
  Qed.

  (* Apply truncate to STACK *)
  Definition trunc_stack v := vec_change v STACK (SBTM_facts.truncate (Vector.nth v STACK)).

  (* Specifes the truncation of STACK*)
  Lemma Truncation_spec_END v:
    vec_pos v Fin4 = [] ->
    vec_pos v Fin0 = [] ->
    (i, TRUNC) // (i, v) ->> 
    (END,vec_change v STACK (rev (remove_leading_falses (rev (vec_pos v STACK))))).
  Proof using STACK_NEQ_FIN0 STACK_NEQ_FIN4.
    intros I1 I2. 
    eapply sss_compute_trans.
    2: eapply sss_compute_trans.
    - apply Truncation_first_loop; now autorewrite with vec_simpl.
    - apply Truncation_first_to_second; now autorewrite with vec_simpl.
    - destruct (leading_false_spec (rev (vec_pos v STACK))) as [n [[l E]|E]].
      + eapply sss_compute_trans.
        2: eapply sss_compute_trans.
        3: eapply sss_compute_trans.
        4: eapply sss_compute_trans.
        * eapply Truncation_second_loop_repeat_false; autorewrite with vec_simpl; [easy | | easy].
        rewrite E. now rewrite app_assoc.
        * eapply Truncation_second_loop_true; autorewrite with vec_simpl; [easy | | easy].
        now rewrite <- app_comm_cons.
        * apply Truncation_third_loop; now autorewrite with vec_simpl.
        * apply Truncation_spec_final; now autorewrite with vec_simpl.
        * bsm sss stop. f_equal.
          rewrite !vec_change_idem.
          rewrite vec_change_comm; [|easy].
          rewrite vec_change_idem.
          rewrite vec_change_comm; [|easy].
          rewrite vec_change_idem.
          rewrite vec_change_comm; [|easy].
          rewrite E.
          rewrite remove_leading_falses_spec.
          rewrite <- I2.
          rewrite vec_change_same.
          rewrite I2.
          now rewrite !app_nil_r.
      + eapply sss_compute_trans.
        2: eapply sss_compute_trans.
        * eapply Truncation_second_loop_repeat_false; autorewrite with vec_simpl; [easy | | easy].
          now rewrite E.
        * apply Truncation_second_loop_empty; now autorewrite with vec_simpl.
        * bsm sss stop. f_equal.
          rewrite vec_change_idem.
          rewrite vec_change_comm; [|easy].
          rewrite vec_change_same.
          rewrite E.
          now rewrite remove_leading_falses_spec_false_only.
  Qed.

End Truncation_Construction.

(* Define truncation program. Use TRUNC on stacks 1 and 3*)
Definition TRUNC_PROG i: list (bsm_instr 5) :=
  TRUNC i Fin1 ++ TRUNC (i + TRUNC_length) Fin3.

(* Apply trunc_stack to stacks 1 and 3*)
Definition trunc_conf (v : vec (list bool) 5) :=
  trunc_stack Fin3 (trunc_stack Fin1 v).
  
(* TRUNC_PROG truncates a stack configuration*)
Lemma TRUNC_PROG_spec i v:
  vec_pos v Fin4 = [] ->
  vec_pos v Fin0 = [] ->
  (i, TRUNC_PROG i) // (i, v) ->> (i + (|TRUNC_PROG i|), trunc_conf v).
Proof.
  intros I1 I2.
  eapply sss_compute_trans;[| eapply sss_compute_trans].
  - eapply subcode_sss_compute;[ | apply (@Truncation_spec_END i Fin1); easy].
    eexists [], _.
    split; [now reflexivity | simpl; lia]. 
  - eapply subcode_sss_compute; [|apply (@Truncation_spec_END (i + TRUNC_length) Fin3)]; rewrite ?vec_change_neq; [eexists (TRUNC i Fin1), _; now split| easy| easy | easy | easy | easy | easy].
  - bsm sss stop. cbn. unfold END, TRUNC_length.
    f_equal; [lia|].
    unfold trunc_conf, trunc_stack.
    rewrite <- !vec_pos_spec.
    rewrite !trunc_spec.
    reflexivity.
Qed.

(* It does not matter if truncation is performed on the SBTM tape or simulated on the BSM stack configuration *)
Lemma trunc_order t:
  trunc_conf (vec_app [|[]|] (SBTM_HALT_to_HaltBSM.encode_tape t)) = vec_app [|[]|] (SBTM_HALT_to_HaltBSM.encode_tape (SBTM_facts.truncate_tape t)).
Proof.
  destruct t as [[l c] r].
  now reflexivity.
Qed.


(* ---Inverse truncation--- *)

(* Define inverse truncation program. To perform inverse truncation on a tape encoded by encode_bsm, one PUSH suffices. *)
Definition INV_TRUNC_PROG := [ @PUSH 5 Fin1 false].

Lemma INV_TRUNC_PROG_length : | INV_TRUNC_PROG | = 1.
Proof. now cbn. Qed.

(* INV_TRUNC_PROG performs inverse truncation on a tape encoded by encode_bsm *)
Lemma INV_TRUNC_spec (n : nat) (Σ : finType) t i: 
  (i, INV_TRUNC_PROG) // (i, encode_bsm t) ->> 
  (i + 1 , vec_app [|[]|] (SBTM_HALT_to_HaltBSM.encode_tape (@complete_encode Σ n t))).
Proof.
  unfold INV_TRUNC_PROG.
  bsm sss PUSH with Fin1 false.
  + apply sc_spec; [cbn; lia | now replace (i - i) with 0 by lia].
  + bsm sss stop.
    unfold complete_encode.
    cbn.
    rewrite truncate_irrel.
    apply pair_equal_spec.
    split; [lia | reflexivity].
Qed.


(* ---Simulation Program--- *)

(* Define the full simulation program. 
  1. Perform inverse truncation
  2. Program from SBTM to BSM (extended to 5 stacks)
  3. Perform truncation
 *)
Definition FULL_PROG M1 q1 i := 
                        INV_TRUNC_PROG ++ 
                        bsm_addstacks 1 (P M1 q1 (i + 1)) ++
                        TRUNC_PROG (i + 1 + (|P M1 q1 (i + 1)|)).
                        

(* If every jump label in a program is either inside the program or at the first label behind the program,
then this holds for each program counter after performing a step *)
Lemma in_code_step_spec i j n t v M M' M'':
  in_code j (i + (|M''|), M) ->
  Forall 
  (fun instr => match instr with 
                  | POP _ k1 k2 => (in_code k1 (i + (|M''|), M) \/ k1 = i + (|M''|) + (|M|)) /\
                                  (in_code k2 (i + (|M''|), M) \/ k2 = i + (|M''|) + (|M|))
                  | _ => True
                  end) M ->
  sss_step (bsm_sss (n:=5)) (i, M'' ++ M ++ M') (j, v) (n, t) ->
  (in_code n (i + (|M''|), M) \/ n = i + (|M''|) + (|M|)).
Proof.
  intros H H1 H2.
  assert (H3:(i + (| M'' |), M) <sc ((i, M'' ++ M ++ M'))) by auto.
  replace j with (fst (j,v)) in H by easy.
  destruct (sss_step_supcode H3 H H2) as [? [l [i' [? [? [H2A [H2B H2C]]]]]]]. clear H2 H3.
  injection H2A. injection H2B. intros H2 H3 H4 H5. clear H2A H2B.
  rewrite Forall_nth in H1.
  cbn in H.
  assert (H6 : j - (i + (|M''|)) < |M|) by lia.
  assert (H7 : j - ((i + (|M''|))) = |l|) by lia.
  specialize (H1 _ (PUSH Fin0 true) H6).
  rewrite H7, H4 in H1.
  rewrite app_nth2 in H1; [|lia].
  replace ((|l|) - (|l|)) with 0 in H1 by lia.
  destruct i' as [m??| ] eqn:I.
  + destruct (vec_pos v m) as [|b y] eqn:E;[|destruct b].
      * apply POP_empty_spec in H2C;[|now apply E].
        destruct H2C as [H2C _].
        destruct H1 as [_ H1].
        rewrite H2C.
        rewrite <- H4 in H1.
        apply H1.
      * apply POP_true_spec with (v' := y) in H2C; [|now apply E].
        destruct H2C as [H2C _].
        rewrite H2C.
        cbn. lia.          
      * apply POP_false_spec with (v' := y) in H2C; [|now apply E].
        destruct H2C as [H2C _].
        destruct H1 as [H1 _].
        rewrite H2C.
        rewrite <- H4 in H1.
        apply H1.
    + apply PUSH_spec in H2C.
      destruct H2C as [H2C _]. rewrite H2C.
      cbn. lia.
Qed.

(* k either lies within the BSM program for SBTM M1 or is the first code label behind the program*)
Definition in_code_or_exact_end k M1 q1 i := 
  in_code k (i , bsm_addstacks 1 (P M1 q1 i)) \/
    k = i + (| bsm_addstacks 1 (P M1 q1 i) |).

(* in_code_or_exact_end holds for each POP of PROG *)
Lemma PROG_JMP_spec M1 q1 i q:
  Forall (fun instr : bsm_instr 4 =>
    match bsm_addstracks' 1 instr with
      | POP _ k1 k2 =>
          @in_code_or_exact_end k1 M1 q1 (i + 1) /\
          @in_code_or_exact_end k2 M1 q1 (i + 1)
      | PUSH _ _ => True
    end) (PROG M1 (i + 1) q).
Proof.
  assert (C := c_spec).
  assert (U := SBTM_HALT_to_HaltBSM.state_number_length M1 q).
  assert (N := SBTM_HALT_to_HaltBSM.state_map_length_spec M1).
  assert (H1 : forall j, j < c -> @in_code_or_exact_end (j + encode_state M1 (i + 1) q) M1 q1 (i + 1)). {
    unfold in_code_or_exact_end.
    rewrite !bsm_length. cbn. rewrite length_map, length_app, length_flat_map_PROG_M. lia.
  }
  assert (H2 : forall j, j < 4 ->  @in_code_or_exact_end (j + (i + 1) + c * num_states M1) M1 q1 (i + 1)). {
    unfold in_code_or_exact_end.
    rewrite !bsm_length. cbn. rewrite length_map, length_app, length_flat_map_PROG_M. simpl. lia.
  }
  assert (H3 : forall q, (@in_code_or_exact_end (encode_state M1 (i + 1) q) M1 q1 (i + 1))). {
    intros q'. unfold in_code_or_exact_end.
    rewrite !bsm_length. cbn. rewrite length_map, length_app, length_flat_map_PROG_M. simpl. 
    assert (H := state_number_length M1 q').
    lia.
  }
  repeat apply Forall_cons; unfold bsm_addstracks', box; try destruct (trans' _ _) as [[[q'?][|]]|]; try split; try apply H1; try apply H2; try apply H3; try lia.
  now apply Forall_nil.
Qed.

(* in_code_or_exact_end holds for each POP of P *)
Lemma P_JMP_spec M1 q1 i:
  Forall (fun instr : bsm_instr 5 =>
    match instr with
      | POP _ k1 k2 =>
          in_code_or_exact_end k1 q1 (i + 1) /\
          in_code_or_exact_end k2 q1 (i + 1)
      | PUSH _ _ => True
    end)
  (bsm_addstacks 1 (P M1 q1 (i + 1))).
Proof.
  assert (C := c_spec).
  assert (L := SBTM_HALT_to_HaltBSM.state_map_length_spec M1).
  unfold P, bsm_addstacks, in_code_or_exact_end.
  rewrite map_cons, map_app.
  apply Forall_cons; [| apply Forall_app; split].
  - cbn.
    assert (H := state_number_length M1 q1).
    rewrite length_map, length_app, length_flat_map_PROG_M.
    lia.
  - apply Forall_map, Forall_flat_map, Forall_nth.
    intros.
    apply PROG_JMP_spec.
  - repeat apply Forall_cons; unfold bsm_addstracks';  try easy;
      rewrite !bsm_length; cbn; rewrite length_map, length_app, length_flat_map_PROG_M; simpl; lia.
Qed.


(* If we make a step from (j,v) to (n, t) in FULL_PROG and j lies within the P subprogram, then:
  1. n lies either within P or is the first code label behind P (first instruction of TRUNC)
  2. if v[4] empty, then t[4] empty
*)
Lemma P_out_code_step_spec M1 q1 i j n t v:
  in_code j (i + 1, bsm_addstacks 1 (P M1 q1 (i + 1))) ->
  sss_step (bsm_sss (n:=5)) (i, FULL_PROG q1 i) (j, v) (n, t) ->
  @in_code_or_exact_end n M1 q1 (i + 1).
Proof.
  intros H H1.
  assert (H2 := @in_code_step_spec i j n t v 
  (bsm_addstacks 1 (P M1 q1 (i + 1))) (TRUNC_PROG (i + 1 + (|P M1 q1 (i + 1)|))) INV_TRUNC_PROG).
  rewrite INV_TRUNC_PROG_length in H2.
  assert (H3 := P_JMP_spec q1 i).
  unfold in_code_or_exact_end in H3.
  now apply (H2 H H3 H1).
Qed.
  
(* If (j,v) lies withing the P subprogram and if we can go from (j, v) to output (out1, out2),
    then we can go to (j', v') where j' is behind the code space of the P subprogram.
    This only holds because of the way FULL_PROG is defined.
    This is used to get from FULL_PROG to the P subprogram.
*)
Lemma P_out_code_spec M1 q1 i j v out1 out2 : 
  (i, FULL_PROG q1 i) //(j, v) ~~> (out1, out2) ->
  in_code (fst (j, v)) (i + 1, bsm_addstacks 1 (P M1 q1 (i + 1))) ->
    exists j' v',(i + 1, bsm_addstacks 1 (P M1 q1 (i + 1))) // (j, v) ->> (j', v') /\ 
    code_end (i + 1, bsm_addstacks 1 (P M1 q1 (i + 1))) <= j'.
Proof.
  intros [[k H] H1] H0.
  revert out1 out2 v i j H H1 H0.
  induction k as [|k IHk]; intros out1 out2 v i j H H1 H0.
  - apply sss_steps_0_inv in H. injection H. intros H2 H3.
    cbn in H0. rewrite <- H3 in H1.
    destruct H1 as [H1 | H1].
    + cbn in H1. lia.
    + simpl in H1.
      rewrite length_map in H0.
      rewrite !length_app in H1.
      rewrite (bsm_length 1) in H1.
      lia.
  - apply sss_steps_S_inv' in H.
    destruct H as [[n t] [H' H'']].
    assert (E := P_out_code_step_spec H0 H').
    assert (I : (i + 1, bsm_addstacks 1 (P M1 q1 (i + 1))) <sc (i, FULL_PROG q1 i)) by (unfold FULL_PROG; auto).
    destruct E as [E | E].
    + specialize (IHk out1 out2 t i n H'' H1 E).
      destruct IHk as [j' [v' [[k' IHk1] IHk2]]].
      exists j', v'.
      split; [|apply IHk2].
      exists (S k').
      apply in_sss_steps_S with (st2 := (n, t)); [apply (sss_step_supcode I H0 H') | apply IHk1].
    + exists n, t.
      split.
      * exists 1.
          apply sss_steps_1.
          apply (sss_step_supcode I H0 H').
      * rewrite E. constructor.
Qed.

(* ---BSM complete simulation--- *)

(* There is a BSM over 5 stacks that simulates TM M*)
Lemma BSM_complete_simulation'' n Σ (M : TM Σ n) i :
  { P |
      (forall q t t', TM.eval M (TM.start M) t q t' ->
      BSM.eval 5 (i, P) (i, encode_bsm t) (i + length P, encode_bsm t')) /\
      (forall t, (exists out, BSM.eval 5 (i, P) (i, encode_bsm t) out) ->
      (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (SBTM_complete_simulation M) as (M1 & q1 & Hf1 & Hb1).
  exists (FULL_PROG q1 i).
  split.
  - clear Hb1.
    intros q t t' H.
    rewrite BSM_sss.eval_iff.
    split; [|right; now constructor].
    unfold encode_bsm.

    (* SBTM complete encode *)
    destruct (Hf1 _ _ _ ((complete_encode t)) H (SBTM_facts.almost_eq_tape_refl (complete_encode t))) as [k [q' [t''' [Hf1A [Hf1B Hf1C]]]]]. clear Hf1.
    apply SBTM_facts.almost_eq_truncate_tape_iff in Hf1C.
    rewrite <- Hf1C.

    eapply sss_compute_trans; [| eapply sss_compute_trans].
    + (* INV_TRUNC*)
      eapply subcode_sss_compute; [| now apply INV_TRUNC_spec].
      unfold FULL_PROG, INV_TRUNC_PROG.
      apply sc_spec; [cbn; lia| now replace (i - i) with 0 by lia].
    + (* P AND ADDSTACKS*)
      eapply subcode_sss_compute; [| now apply (BSM_addstacks' [|[]|] (SBTM_HALT_to_HaltBSM.simulation_output' _ _ _ _ _ _ _ Hf1A Hf1B))].
      eexists (INV_TRUNC_PROG), _.
      split; [now reflexivity| cbn; lia].
    + (* TRUNC*)
      unfold FULL_PROG.
      rewrite !length_app, bsm_length, INV_TRUNC_PROG_length, !Nat.add_assoc.
      rewrite <- trunc_order.
      eapply subcode_sss_compute; [| apply TRUNC_PROG_spec; now destruct t''' as [[??]?]].
      eexists _, [].
      split; [now rewrite app_nil_r, app_assoc|].
      rewrite !length_app, bsm_length. 
      cbn.
      lia.

  - intros t H.
    clear Hf1.
    apply Hb1.
    clear Hb1.
    destruct H as [[out1 out2] H].
    rewrite BSM_sss.eval_iff in H. 
    destruct H as [H1 H2].
    (* REMOVE INVERSE TRUNCATION*)
    assert (INV : (i, FULL_PROG q1 i) // 
            (i + 1, vec_app [|[]|](SBTM_HALT_to_HaltBSM.encode_tape (complete_encode t))) ->> (out1, out2)).
    {
      destruct H1 as [k H1].
      apply sss_steps_inv in H1.
      destruct H1 as [[H1A H1B] | [k' [[st2A st2B] [H1A [H1B H1C]]]]].
      + injection H1B. clear H1B. intros H1B H1C.
        assert (H : in_code i ((i, FULL_PROG q1 i))) by (simpl; lia).
        rewrite <- H1C in H2. 
        destruct (in_out_code H H2).
      + apply sss_step_subcode_inv with (ii := PUSH Fin1 false) in H1B. 
        * apply PUSH_spec in H1B.
          destruct H1B as [H1B H1D].
          rewrite H1B, H1D in H1C.
          exists k'.
          simpl.
          rewrite <- truncate_irrel.
          apply H1C.
        * eexists [], _.
          split; [now reflexivity|simpl;lia]. 
    }

    (* i + 1 is in code of core program P*)
    assert (IN_CODE : in_code (fst (i + 1,  vec_app [|[]|](SBTM_HALT_to_HaltBSM.encode_tape (complete_encode t)))) (i + 1, bsm_addstacks 1 (P M1 q1 (i + 1)))); [simpl; rewrite (bsm_length 1); lia|].
    (* REMOVE TRUNCATION *)
    destruct (P_out_code_spec (conj INV H2) IN_CODE) as [j' [v' [INV1 INV2]]].
    unfold code_end, fst, snd in INV2.
    clear INV H1 IN_CODE H2.
    (* REMOVE ADD STACKS*)
    destruct (@BSM_addstacks_bwd' 4 (i + 1) (P M1 q1 (i + 1)) 1 (i + 1) (SBTM_HALT_to_HaltBSM.encode_tape (complete_encode t)) [|[]|] (j',v') INV1) as [o [v'' [BWD1 BWD2]]]. clear INV1.
    injection BWD1. intros BWD1A BWD1B. clear BWD1.
    (* INV SIM*)
    unfold code_end, fst, snd in INV2.
    rewrite (bsm_length 1) in INV2.
    destruct (Nat.le_exists_sub (i + 1 + (| P M1 q1 (i + 1) |)) j' INV2) as [m [LE _]].
    rewrite Nat.add_comm in LE.
    rewrite LE in BWD1B.
    rewrite <- BWD1B in BWD2.
    rewrite <- Nat.add_assoc in BWD2.
    apply (SBTM_HALT_to_HaltBSM.inverse_simulation' M1 q1 (i + 1) (complete_encode t) ((| P M1 q1 (i + 1)|) + m) v'').
    split; [apply BWD2 |].
    right. simpl. lia.
Qed.

(* Lift simulation to m + 5 stacks*)
Lemma BSM_complete_simulation' n Σ (M : TM Σ n) m i :
  { P |
      (forall q t t', TM.eval M (TM.start M) t q t' ->
       forall v'', BSM.eval (m + 5) (i, P) (i, Vector.append v'' ((encode_bsm t))) (i + length P, Vector.append v'' ((encode_bsm t')))) /\
      (forall t v'', (exists out, BSM.eval (m + 5) (i, P) (i, Vector.append v'' ((encode_bsm t))) out) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (BSM_complete_simulation'' M i) as [P [H1 H2]].
  destruct (BSM_addstacks i P m) as [P' [H3 [H4 H5]]].
  exists P'.
  split.
  - intros q t t' H.
    apply H4.
    rewrite <- H3.
    apply (H1 q t t' H).
  - intros t v'' [out H].
    apply H2.
    apply (H5 (encode_bsm t) v'' i out).
    apply H.
Qed.

(* BSM simulation with sss_terminates *)
Lemma BSM_complete_simulation n Σ (M : TM Σ n) m  i :
    { P |
      (forall q t t', TM.eval M (TM.start M) t q t' ->
       forall v'', BSM.eval (m + 5) (i, P) (i, Vector.append v'' ((encode_bsm t))) (i + length P, Vector.append v'' ((encode_bsm t')))) /\
      (forall t v'', (sss.sss_terminates (bsm_sss (n := (m + 5))) (i, P) (i, Vector.append v'' ((encode_bsm t)))) ->
       (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (@BSM_complete_simulation' n Σ M m i) as (P & H1 & H2).
  exists P. split; [exact H1|].
  intros t v'' ([out1 out2] & H % BSM_sss.eval_iff). eapply H2. eauto.
Qed.

(* Check all possible cases of pos 5*)
Lemma Fin5_cases (P : pos 5 -> Prop) :
   P Fin0 -> P Fin1 -> P Fin2 -> P Fin3 -> P Fin4 -> forall p, P p.
Proof.
  intros H0 H1 H2 H3 H4.
  repeat (intros p; eapply (Fin.caseS' p); clear p; [ eauto | ]).
  intros p. inversion p.
Qed.

Lemma PREP1_spec k Σ n :
{ PREP1 : list (bsm_instr ((1 + k) + 5)) | forall v : Vector.t nat k,
    (0, PREP1) // (0, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) (Vector.const [] 5)) ->>
                  (length PREP1, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) ((@encode_bsm Σ _ (Vector.const niltape n)))) }.
Proof.
  exists (
      push_exactly (pos_right (1 + k) Fin0) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin0])
      ++ push_exactly (pos_right (1 + k) Fin1) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin1])
      ++ push_exactly (pos_right (1 + k) Fin2) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin2])
      ++ push_exactly (pos_right (1 + k) Fin3) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin3])
      ++ push_exactly (pos_right (1 + k) Fin4) ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin4])).
  intros v.
  rewrite <- !vec_app_spec.
  (* Keeps expressions smaller *)
  assert (H0 : forall i, @vec_pos (list bool) _ [|[]; []; []; []; []|]  i = []). {
    do 5 (intros i; apply (Fin.caseS' i); [easy| ]; clear i).
    now apply (Fin.case0).
  }
  eapply subcode_sss_compute_trans; 
  [| eapply (push_exactly_spec (pos_right (1 + k) Fin0) 0 ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin0]))| ];
  [now auto |].
  rewrite vec_change_app_right, vec_pos_app_right, <- vec_pos_spec, H0, vec_pos_spec, encode_bsm_at0.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin1) _ ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin1])). 1:auto.
  rewrite vec_change_app_right, vec_pos_app_right, <- vec_pos_spec, H0, vec_pos_spec, encode_bsm_at1.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin2) _ ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin2])). 1:auto.
  rewrite vec_change_app_right, vec_pos_app_right, <- vec_pos_spec, H0, vec_pos_spec, encode_bsm_at2.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin3) _ ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin3])). 1:auto.
  rewrite vec_change_app_right, vec_pos_app_right, <- vec_pos_spec.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin4) _ ((@encode_bsm Σ _ (Vector.const niltape n))@[Fin4])). 1:auto.
  bsm sss stop. apply f_equal2. 1:rewrite !length_app; lia.
  rewrite !vec_change_app_right, !app_nil_r, vec_pos_app_right.
  reflexivity.
Qed.

(*
  encode_bsm always returns the following stacks:
  0 = []
  1 = [false]
  2 = [true]
  3: no further specification
  4 = []
*)
Lemma encode_bsm_ext Σ n v :
  @encode_bsm Σ n v = [] ::: [] ::: [true] ::: ((encode_bsm v)@[Fin3]) ::: [] ::: vec_nil.
Proof.
  eapply vec_pos_ext. eapply Fin5_cases.
  - now rewrite vec_pos_spec, encode_bsm_at0.
  - now rewrite vec_pos_spec, encode_bsm_at1.
  - now rewrite vec_pos_spec, encode_bsm_at2.
  - reflexivity.
  - now rewrite vec_pos_spec, encode_bsm_at4.
Qed.

Opaque encode_bsm.

Lemma PREP2_spec'' k (Σ : finType) (x : pos k) i s b :
{ PREP2 : list (bsm_instr ((1 + k) + 5)) | 
  length PREP2 = 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)) /\
  forall v : Vector.t (list bool) k,  forall n, forall t : Vector.t (tape Σ) n, forall m m',
    v @[x] = repeat true m ->
      (i, PREP2) // (i,                Vector.append ([] ::: v) ((@encode_bsm Σ _ (encNatTM s b m' ::: t)))) ->>
                    (i + length PREP2, Vector.append ([] ::: vec_change v x nil) ((@encode_bsm Σ _ (encNatTM s b (m + m') ::: t)))) }.
Proof.
  exists (
        POP (pos_left 5 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)))
        :: pop_many (pos_right (1 + k) Fin3) (length (strpush_common_short s b)) (1 + i) 
        ++ push_exactly (pos_right (1 + k) Fin3) (strpush_succ s b)
        ++ POP (pos_left 5 Fin0) 0 i
        :: nil).
  split.
  { cbn. rewrite !length_app. cbn. rewrite pop_many_length, push_exactly_length. lia. }
  intros v n t m m' Hx.
  induction m in v, m', Hx |- *.
  - bsm sss POP empty with (pos_left 5 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b))). {
    rewrite <-!vec_app_spec, vec_pos_app_left. cbn. rewrite vec_pos_spec. easy.
    }
    bsm sss stop. apply f_equal2.
      + cbn. rewrite !length_app, pop_many_length, push_exactly_length. cbn. lia.
      + cbn in Hx. rewrite <- Hx. now rewrite <- vec_pos_spec, vec_change_same.
  - bsm sss POP one with (pos_left 5 (pos_right 1 x)) 0 (i + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b))) (repeat true m).
     { rewrite <- !vec_app_spec, vec_pos_app_left. cbn.
        rewrite vec_pos_spec, Hx. reflexivity. }
    rewrite <- vec_app_spec, vec_change_app_left.
    replace ([] ::: v) with (vec_app [|[]|] v) by (rewrite vec_app_spec; easy).
    rewrite vec_change_app_right.
    eapply subcode_sss_compute_trans. 2: eapply (pop_many_spec (pos_right (1 + k) Fin3) (length (strpush_common_short s b)) (1 + i)). 1:auto.
    rewrite vec_change_app_right, vec_pos_app_right, encode_bsm_ext.
    simpl.
    eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin3) _ (strpush_succ s b)).
    { eexists (POP _ _ _ :: pop_many _ _ _), ([POP _ _ _]). split; [now reflexivity|].
      cbn. rewrite pop_many_length. lia. }
    rewrite vec_change_app_right, vec_pos_app_right.
    simpl.
    bsm sss POP empty with (pos_left 5 Fin0) 0 i. {
      eexists (POP _ _ _ :: pop_many _ _ _ ++ push_exactly _ _), []. cbn. simpl_list. split; [now reflexivity|].
      rewrite pop_many_length, push_exactly_length. lia. }
    specialize IHm with (m' := (S m')).
    match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : Vector.t (list bool) ((1 + k) + 5)); enough (st = ev) as ->; subst ev end; [
    match goal with [ |- sss_compute _ _ _ (_, ?st) ] => evar (ev : Vector.t (list bool) ((1 + k) + 5)); enough (st = ev) as ->; subst ev end|].
    + eapply IHm with (v := vec_change v x (repeat true m)). now rewrite <- vec_pos_spec, vec_change_eq.
    + rewrite vec_change_idem; now replace (S (m + m')) with (m + S m') by lia.
    + rewrite vec_app_spec.
      f_equal; [now rewrite vec_app_spec| now rewrite <- encode_bsm_succ].
Qed.

Definition PREP2''_length (Σ : finType) (s b : Σ) := proj1_sig (encode_bsm_zero s b) + length (strpush_zero s b) + 2 + (length (strpush_common_short s b)) + length ((strpush_succ s b)).

Lemma PREP2_spec' k (Σ : finType) (x : pos k) i s b n :
{ PREP2 : list (bsm_instr ((1 + k) + 5)) | 
  length PREP2 = PREP2''_length s b  /\
  forall v : Vector.t (list bool) k, forall t : Vector.t (tape Σ) n, forall m,
    v @[x] = repeat true m ->
      (i, PREP2) // (i,                Vector.append ([] ::: v) ((@encode_bsm Σ _ t))) ->>
                    (i + length PREP2, Vector.append ([] ::: vec_change v x nil) ((@encode_bsm Σ _ (encNatTM s b m ::: t)))) }.
Proof.
  unfold PREP2''_length.
  destruct (encode_bsm_zero s b) as [n' Hn'].
  destruct (PREP2_spec'' x (i + n' + length (strpush_zero s b)) s b) as [PREP2 [Hl2 H]].
  exists (
      pop_many (pos_right (1 + k) Fin3) n' i
       ++ push_exactly (pos_right (1 + k) Fin3) (strpush_zero s b)
       ++ PREP2).
  split.
  {  cbn. rewrite !length_app, pop_many_length, push_exactly_length. cbn in Hl2. lia. }
  intros v t m Hm.
  eapply subcode_sss_compute_trans. 2: eapply (pop_many_spec (pos_right (1 + k) Fin3) n' i). 1:auto.
  rewrite <- vec_app_spec, vec_change_app_right, vec_pos_app_right, encode_bsm_ext.
  simpl.
  eapply subcode_sss_compute_trans. 2: eapply (push_exactly_spec (pos_right (1 + k) Fin3) _ (strpush_zero s b)).
  { eexists (pop_many _ _ _), PREP2. split.  1: reflexivity. rewrite pop_many_length. lia. }
  rewrite vec_change_app_right, vec_pos_app_right.
  simpl.
  specialize H with (m' := 0) (v := v) (1 := Hm). replace (m + 0) with m in H by lia.
  eapply subcode_sss_compute_trans. 2:{
  match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : Vector.t (list bool) ((1 + k) + 5)); enough (st = ev) as ->; subst ev end.
  1: match goal with [ |- sss_compute _ _ (?st, _) _ ] => evar (ev : nat); enough (st = ev) as ->; subst ev end.
  - eapply H.
  - rewrite push_exactly_length. lia.
  - rewrite vec_app_spec. f_equal.
    now rewrite <- Hn', <- encode_bsm_ext.
  }
  { eexists (pop_many _ _ _ ++ push_exactly _ _), []. rewrite app_nil_r. split.  1: now simpl_list. rewrite length_app, pop_many_length, push_exactly_length. lia. }
  bsm sss stop. apply f_equal2; [|reflexivity].
  now rewrite !length_app, pop_many_length, push_exactly_length, !Nat.add_assoc.
Qed.

Fixpoint PREP2' (Σ : finType) (s b : Σ) k'' (k' : nat)  (i : nat) (n : nat) : list (bsm_instr ((1 + (k' + k'') + 5))).
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
  - cbn - [mult]. destruct PREP2_spec' as (? & ? & ?). cbn. rewrite length_app. cbn in e. rewrite e.
    rewrite BSM_cast_length. cbn in IHk'. rewrite IHk'. lia.
Qed.

Notation "v1 +++ v2" := (Vector.append v1 v2) (at level 60).

Lemma vec_list_encode_bsm Σ n1 n2 v1 v2 :
  vec_list v1 = vec_list v2 ->
  vec_list (@encode_bsm Σ n1 v1) = vec_list (@encode_bsm Σ n2 v2).
Proof.
  intros H.
  assert (n1 = n2).  1: eapply (f_equal (@length _)) in H.  1: rewrite !vec_list_length in H.  1: assumption.
  subst. apply vec_list_inj in H. now subst.
Qed.

Lemma PREP2_spec_strong (Σ : finType) i s b k' k'' v (v' : Vector.t nat k'') n (t : Vector.t (tape Σ) n) :
    (i, @PREP2' Σ s b k'' k'  i n) //
    (i,                                    ([] ::: Vector.map (fun n => repeat true n) v +++ Vector.const [] k'') +++  (@encode_bsm Σ _ (Vector.map (encNatTM s b) v' +++ t))) ->>
    (i + length(@PREP2' Σ s b k'' k' i n), ([] ::: Vector.const [] (k' + k'')  +++  (@encode_bsm Σ _ (Vector.map (encNatTM s b) (v +++ v') +++ t)))).
Proof.
  induction k' in k'', v, v', i |- *.
  - cbn. bsm sss stop. f_equal.  1: lia. f_equal. revert v. apply (Vector.case0). reflexivity.
  - unshelve edestruct (vector_inv_back v) as [(y, vl) Hv].  1: abstract lia. cbn - [minus mult].
    assert (k' < S k') as Hlt by lia.
    match goal with [ |- context[proj1_sig ?y]] => destruct y as [PREPIT [HlP HPREP]]; cbn [proj1_sig] end.
    eapply subcode_sss_compute_trans with (P := (i, _)). { cbn - [minus mult]. eexists [], _. cbn - [mult minus]. split.  1: reflexivity. now rewrite Nat.add_0_r. }
    1: cbn - [minus mult].  1: cbn - [minus mult] in HPREP.  1: specialize HPREP with (m := v@[Fin.of_nat_lt Hlt]).  1: cbn [mult] in HPREP.
    Arguments Fin.of_nat_lt _ {_ _}.  1: refine (HPREP _ _ _). { rewrite <- !vec_pos_spec, <- !vec_map_spec, <- !vec_app_spec. eapply nth_error_vec_list.
    rewrite @vec_list_vec_app with (n := S k') (m := k''), vec_list_vec_map.
    rewrite nth_error_app1. 2: rewrite length_map, vec_list_length; lia.
    eapply map_nth_error.
    erewrite nth_error_vec_list.
    all:eapply (nth_error_nth' _ 0); rewrite vec_list_length; lia. }
    pose proof (@vec_list_vec_map nat (list bool)) as Heq. specialize (Heq) with (n := (S (k' + k''))).
    match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : vec (list bool) (S (S (k' + k'' + 5)))); enough (st = ev) as ->; subst ev end.
    1: match goal with [ |- sss_compute _ _ _ (_, ?st) ] => evar (ev : vec (list bool) (S (S (k' + k'' + 5)))); enough (st = ev) as ->; subst ev end.
    1: match goal with [ |- sss_compute _ _ _ (?st, _) ] => evar (ev : nat); enough (st = ev) as ->; subst ev end.
    1: cbn - [minus mult] in HlP.  1: rewrite <- HlP.
    1: eapply subcode_sss_compute with (P := (i + (|PREPIT|), _)). { exists PREPIT, []. split. 2:reflexivity. now simpl_list. }
    1: specialize IHk' with (v := vl) (v' := y ::: v') (k'' := S k'').  1: apply BSM_cast_spec.
    1: eapply IHk'.
    + rewrite !length_app, BSM_cast_length, !PREP2'_length.
      setoid_rewrite PREP2'_length. clear. lia.
    + cbn. f_equal. eapply vec_list_inj.
      rewrite <- !vec_map_spec, <- !vec_app_spec. cbn [vec_list]. rewrite !vec_list_cast, !vec_list_vec_app, !vec_list_const.
      rewrite app_comm_cons. f_equal.
      1: now replace  (k' + S k'') with (S (k' + k'')) by lia. f_equal. subst v.
      rewrite !vec_app_spec.
      rewrite vec_map_spec.
      rewrite !Vector_map_app.
      pose proof (@Vector_map_app) as Vm. specialize Vm with (k1 := S k') (k2 := k''). cbn in Vm. rewrite Vm. clear Vm.
      eapply vec_list_inj, vec_list_encode_bsm.
      rewrite <- !vec_map_spec, <- !vec_app_spec.
      rewrite !vec_list_vec_app.
      setoid_rewrite <- vec_map_spec. rewrite !vec_list_vec_map. cbn[vec_list map].
      pose proof (@vec_list_vec_app (tape Σ) (S (k' + k'')) n). cbn [plus] in H. rewrite H. clear H.
      pose proof (@vec_list_vec_app (tape Σ) (S k') k''). cbn [plus] in H. rewrite H. clear H.
      rewrite !vec_list_vec_map. cbn[vec_list map]. simpl_list.
      rewrite !vec_list_cast, vec_list_vec_app. cbn. simpl_list. reflexivity.
    + eapply vec_list_inj. rewrite <- !vec_map_spec, <- !vec_app_spec. cbn [vec_list].
      rewrite !vec_list_cast.
      pose proof (@vec_list_vec_app (list bool) (S (k' + k'')) 5). cbn [plus] in H. rewrite !H. clear H.
      pose proof (@vec_list_vec_app (list bool) (S (k' + S k'')) 5). cbn [plus] in H. rewrite !H. clear H.
      cbn [vec_list app].
      f_equal.
      rewrite !vec_list_vec_app.
      cbn [Vector.map]. rewrite vec_app_cons. f_equal. 2:{
      cbn.
      rewrite Hv, <- vec_pos_spec.
      repeat f_equal.
      eapply nth_error_vec_list.
      rewrite vec_list_cast, <- vec_app_spec, vec_list_vec_app, nth_error_app2; rewrite !vec_list_length, ?Nat.sub_diag; try lia.
      reflexivity. }
      rewrite vec_list_vec_change.
      pose proof (@vec_list_vec_app (list bool) (S k') k''). cbn [plus] in H. rewrite !H. clear H.
      setoid_rewrite <- vec_map_spec.
      rewrite !vec_list_vec_map, !vec_list_const.
      rewrite update_app_left. 2: rewrite Fin.to_nat_of_nat; cbn; rewrite length_map, vec_list_length; lia.
      subst v. rewrite vec_list_cast. rewrite <- vec_app_spec. rewrite vec_list_vec_app. cbn [vec_list]. rewrite Fin.to_nat_of_nat. cbn.
      rewrite map_app, update_app_right.  2: rewrite length_map, vec_list_length; lia.
      rewrite length_map, vec_list_length, Nat.sub_diag. cbn. now simpl_list.
Qed.

Lemma PREP2_spec k (Σ : finType) i s b  n :
  { PREP2 | forall v (t : Vector.t (tape Σ) n),
    (i, PREP2) //
    (i,                ([] ::: Vector.map (fun n => repeat true n) v) +++  (@encode_bsm Σ _ t)) ->>
    (i + length PREP2, ([] ::: Vector.const [] k                      +++  (@encode_bsm Σ _ (Vector.map (encNatTM s b) v +++ t)))) }.
Proof.
  unshelve eexists (BSM_cast (@PREP2' Σ s b 0 k  i n) _).  1: abstract lia. intros v t.
  match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : vec (list bool) (S k + 5)); enough (st = ev) as ->; subst ev end.
  1: match goal with [ |- sss_compute _ _ _ (_, ?st) ] => evar (ev : vec (list bool) (S k + 5)); enough (st = ev) as ->; subst ev end.
  1: rewrite <- BSM_cast_spec.
  1: rewrite BSM_cast_length.  1: eapply PREP2_spec_strong.
    - eapply vec_list_inj.
      rewrite <- !vec_app_spec. cbn. rewrite vec_list_cast, !vec_list_vec_app, !vec_list_const.
      f_equal. f_equal.  1: now rewrite Nat.add_0_r.
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
  exists (pop_many (pos_right k Fin3) n' i
      ++ push_exactly (pos_right k Fin3) str).
  intros v t.
  eapply subcode_sss_compute_trans with (P := (i, pop_many (pos_right k Fin3) n' i)).  1: auto.
  1: eapply pop_many_spec.
  rewrite <- vec_app_spec, vec_change_app_right.
  eapply subcode_sss_compute_trans with (P := (n' + i, push_exactly (pos_right k Fin3) str)).
  { exists (pop_many (pos_right k Fin3) n' i), []. split.  1: now rewrite app_nil_r. rewrite pop_many_length; lia. }
  1: eapply push_exactly_spec. bsm sss stop.
  f_equal.  1: rewrite length_app, pop_many_length, push_exactly_length, push_exactly_length; lia.
  rewrite vec_change_app_right, vec_app_spec, !vec_pos_app_right, vec_change_idem, encode_bsm_ext.
  simpl.
  now rewrite <- H, encode_bsm_ext.
Qed.


Lemma PREP_spec k n Σ s b :
  { PREP | forall v : Vector.t nat k,
    (0, PREP) // (0, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) (Vector.const [] 5)) ->>
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
  bsm sss stop. f_equal. rewrite !length_app. now rewrite Nat.add_assoc.
Qed.

Lemma skipn_plus n m {X} (l : list X) : skipn n (skipn m l) = skipn (n + m) l.
Proof.
  induction m in n, l |- *.
  - cbn. f_equal. lia.
  - cbn. destruct l.  1: cbn.  1: destruct n; reflexivity. rewrite IHm. now replace (n + S m) with (S n + m) by lia.
Qed.

Lemma vec'_change_app_right {X : Type} (n m : nat) (v1 : vec X n) (v2 : vec X m)  (p : pos m) (x : X) :
  vec_change (v1 +++ v2) (pos_right n p) x = v1 +++ (vec_change v2 p x).
Proof. rewrite <- !vec_app_spec. apply vec_change_app_right. Qed.

Lemma vec'_pos_app_right {X : Type} (n m : nat) (v : vec X n) (w : vec X m) (i : pos m) :
  vec_pos (v +++ w) (pos_right n i) = vec_pos w i.
Proof. rewrite <- !vec_app_spec. apply vec_pos_app_right. Qed.

Lemma flat_map_encode_symbol_inj v1 v2 :
  flat_map encode_symbol v1 = flat_map encode_symbol v2 -> v1 = v2.
Proof.
  revert v2.
  induction v1 as [| a l1 IHl1]; intros v2 H; destruct v2 as [| b l2]; [easy| inversion H | inversion H|]; destruct a,b; [|inversion H|inversion H|];
  f_equal; apply IHl1; cbn in H; injection H; easy.
Qed.
  

Lemma POSTP_spec' k n (Σ : finType) s b i :
  { POSTP | forall v : Vector.t _ k, forall t : Vector.t (tape Σ) (k + n), forall m m', exists out,
   (i, POSTP) // (i, Vector.append (repeat true m' ## v) ([] ::: [] ::: [true] ::: skipn (length (strpush_common s b)) ((encode_bsm (encNatTM s b m ## t))@[Fin3]) ::: [] ::: vec_nil)) ->>
                 (i + length POSTP, Vector.append (repeat true (m + m') ## v) (out ))
  }.
Proof.
    pose (THESYM := flat_map encode_symbol (encode_sym
  (projT1
     (projT2
        (FinTypes.finite_n
           (finType_CS
              (boundary +
               sigList (EncodeTapes.sigTape Σ)))))
     (inr (sigList_X (EncodeTapes.UnmarkedSymbol s)))))).
  exists (
      pop_exactly (pos_right (1 + k) Fin3) (pos_right (1 + k) Fin4) (i + 6 + 2 * length THESYM) THESYM i
      ++  PUSH (pos_left 5 Fin0) true
      ::  pop_many (pos_right (1 + k) Fin3) 4 (i + 1 + 2 * length THESYM)
      ++  POP (pos_right (1 + k) Fin0) i i :: nil).

  intros.
  induction m in i, m' |- *.
  - pose proof (encode_bsm_zero s b) as [n' Hn'].
    rewrite Hn'. unfold strpush_zero. rewrite <- !app_assoc.
    rewrite skipn_app'; [ | reflexivity].
    edestruct (@pop_exactly_spec2 (1 + k + 5) (pos_right (1 + k) Fin3) (pos_right (1 + k) Fin4) (i + 6 + 2 * length THESYM)) as [x' Hpop].
    1:{ intros ? % pos_right_inj. discriminate. }
    3:{ eexists. eapply subcode_sss_compute_trans. 2: eapply Hpop.  1: auto.  1: eexists [], _.  1: cbn.  1: split. 2: lia.  1: reflexivity.
        bsm sss stop. apply f_equal2. 1: rewrite !length_app, pop_exactly_length.  1: cbn - [mult].  1: lia.
        apply vec'_change_app_right. }
    2:{ apply vec'_pos_app_right. }
       rewrite vec'_pos_app_right. cbn.
    intros (l' & Hneq).
    unfold THESYM in Hneq. eapply utils_list.list_app_inj in Hneq as [].
    2: repeat rewrite encode_length; now rewrite !length_encode_sym.
    eapply flat_map_encode_symbol_inj in H.
    eapply encode_sym_inj in H.
    clear - H. destruct FinTypes.finite_n as [? [f H']]; cbn in *.
    destruct H' as [g [_ H2]]. eapply (f_equal g) in H. now rewrite !H2 in H.
  - edestruct IHm as [out IH]. eexists.
    rewrite encode_bsm_succ. unfold strpush_succ. fold THESYM. rewrite <- !app_assoc.
    rewrite skipn_app' by reflexivity.
    eapply subcode_sss_compute_trans. 2: eapply pop_exactly_spec1. { eexists [], _. split. 2:cbn;lia. { cbn. reflexivity. } }
    1: { intros ? % pos_nxt_inj % pos_right_inj. discriminate. }
    1: { cbn. rewrite vec'_pos_app_right. cbn. 1: reflexivity. }
    1: { apply vec'_pos_app_right. }
    rewrite <- !vec_app_spec. rewrite vec_app_cons. cbn [vec_change pos_S_inv]. rewrite vec_change_app_right. cbn [vec_change pos_S_inv].
    bsm sss PUSH with  (pos_left 5 Fin0) true.  1: eexists (pop_exactly (pos_right (1 + k) pos3) (pos_right (1 + k) pos4)
    (i + 6 + 2 * (| THESYM |)) THESYM i), _.  1: { cbn. split. 1: reflexivity. rewrite pop_exactly_length. lia. }
    rewrite <- vec_app_cons. rewrite vec_change_app_left. cbn [vec_change pos_S_inv]. rewrite vec_pos_app_left. cbn [vec_pos pos_S_inv].
    eapply subcode_sss_compute_trans. 2: eapply (@pop_many_spec (1 + k + 5) (pos_right (1 + k) Fin3) 4).
    { eexists (pop_exactly (pos_right (1 + k) Fin3) (pos_right (1 + k) Fin4) (i + 6 + 2 * length THESYM) THESYM i
    ++  PUSH (pos_left 5 Fin0) true :: nil), (POP (pos_right (1 + k) Fin0) i i :: nil). split.  1: simpl_list.  1: cbn - [mult].  1: repeat f_equal. 1-8: cbn; lia.
    rewrite length_app, pop_exactly_length. cbn. lia. }
    rewrite vec_change_app_right. cbn [vec_change pos_S_inv]. rewrite vec_pos_app_right.
    cbn [vec_pos pos_S_inv]. rewrite skipn_plus.
    bsm sss POP empty with (pos_right (1 + k) Fin0) i i.  1: eexists (_ ++ _ :: _), [].  1: split.  1: rewrite app_nil_r.  1: simpl_list.  1: reflexivity.  1: rewrite length_app, pop_exactly_length.
    1: cbn.  1: lia.  1: now rewrite vec_pos_app_right.
    match goal with [ |- sss_compute _ _ (_, ?st) _ ] => evar (ev : Vector.t (list bool) ((1 + k) + 5)); enough (st = ev) as ->; subst ev end.
    1: match goal with [ |- sss_compute _ _ (_, _) (_, ?st) ] => evar (ev : Vector.t (list bool) ((1 + k) + 5)); enough (st = ev) as ->; subst ev end.
    1: eapply IH.  1: instantiate (1 := S m').  1: replace (m + S m') with (S (m + m')).  1: cbn [repeat plus].  1: rewrite vec_app_cons.
    1: now rewrite vec_app_spec.  1: lia.
    cbn [repeat]. rewrite vec_app_spec.
    assert (4 + (| strpush_common_short s b |) = | strpush_common s b |).
    { unfold strpush_common. rewrite length_app. cbn. lia. }
    now rewrite <- H.
Qed.

Lemma POSTP_spec k n (Σ : finType) s b i :
  { POSTP | forall v : Vector.t _ k, forall t : Vector.t (tape Σ) (k + n), forall m, exists out,
   (i, POSTP) // (i, Vector.append ([] ## v) ((encode_bsm (encNatTM s b m ## t)))) ->>
                 (i + length POSTP, Vector.append (repeat true m ## v) (out ))
  }.
Proof.
  destruct (@POSTP_spec' k n Σ s b (i + (length (strpush_common s b)))) as [POSTP HPOST].
  specialize HPOST with (m' := 0).
  exists (pop_many (pos_right (1 + k) Fin3) (length (strpush_common s b)) i ++ POSTP).
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
  rewrite Nat.add_0_r in HPOST'. rewrite vec_app_spec. cbn [repeat] in HPOST'.
  replace ((|strpush_common s b|) + i) with (i + (|strpush_common s b|)) by lia.
  eapply subcode_sss_compute_trans.
  2: apply HPOST'.  1: eexists _, [].  1: split.  1: now rewrite app_nil_r.  1: rewrite pop_many_length.  1: lia.
  bsm sss stop. f_equal. rewrite length_app, pop_many_length. cbn. lia.
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
  - intros v m (q & t & Heval & Hhd)% HM1. rewrite (Vector.eta t), Hhd in Heval.
    eapply Hf in Heval.
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
      1: rewrite <- length_app.  1: eapply HPOSTP'.
      bsm sss stop. reflexivity.
    + cbn. right. rewrite !length_app. lia.
  - intros. edestruct Hb as (? & ? & HbH). 2:eapply HM2. 2:eapply HbH.
    eapply subcode_sss_terminates.
    2:{ eapply subcode_sss_terminates_inv.  1: eapply bsm_sss_fun.
    1: eapply H. 2:{ split.  1: eapply HPREP. cbn. lia. } auto. }
    auto.
Qed.
