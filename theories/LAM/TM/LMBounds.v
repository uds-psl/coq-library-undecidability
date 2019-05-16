(** * PrettyBounds for LM *)

From Undecidability Require Import TM.PrettyBounds.PrettyBounds.
From Undecidability Require Import TM.PrettyBounds.BaseCode.
From Undecidability Require Import TM.PrettyBounds.MaxList.

From Undecidability.LAM Require Import LM_heap_def TM.Alphabets.
From Undecidability.LAM.TM Require Import CaseCom.
From Undecidability.LAM.TM Require Import JumpTargetTM.



(** ** LM step functions *)


(** Add match lemma for Token *)
Lemma dominatedWith_match_Tok com y1 y2 y3 y4 z c1 c2 c3 c4:
  (com = appT -> y1 <=(c1) z) ->
  (com = lamT -> y2 <=(c2) z) ->
  (com = retT -> y3 <=(c3) z) ->
  (forall x, com = varT x -> y4 x <=(c4) z) ->
  match com with
  | appT => y1
  | lamT => y2
  | retT => y3
  | varT x => y4 x
  end <=(max c1 (max c2 (max c3 c4))) z .
Proof with reflexivity + apply Nat.mul_le_mono; eauto 4 using le_trans, Nat.le_max_r,Nat.le_max_l.
  intros H1 H2 H3 H4. unfold dominatedWith in *.
  destruct com.
  - rewrite H4...
  - rewrite H1...
  - rewrite H2...
  - rewrite H3...
Qed.

Smpl Add 12
     match goal with
     | [ |- (match _ with appT => _ | _ => _ end) <=(_) _ ] =>
       let H := fresh in (eapply dominatedWith_match_Tok;[intros H..|intros ? H]);try rewrite !H
     end : domWith_match.


(** ** Sizes for (atomic) commands *)

Lemma size_ACom_singleton (t : ACom) :
  size [ACom2Com t] = 4.
Proof. destruct t; cbn; cbv; reflexivity. Qed.

Lemma size_ACom_singleton' (t : ACom) :
  size [t] = 3.
Proof. destruct t; cbn; cbv; reflexivity. Qed.

Lemma size_ACom (t : ACom) :
  size t = 1.
Proof. unfold size. destruct t; cbn; reflexivity. Qed.

Lemma size_ACom' (t : ACom) :
  size (ACom2Com t) = 2.
Proof. unfold size. destruct t; cbn; reflexivity. Qed.

Lemma size_Var (n : Var) :
  size (varT n) = 2 + n.
Proof. unfold size. cbn. simpl_list. rewrite repeat_length. cbn. omega. Qed.

Lemma size_Var' (n : Var) :
  size (varT n) = 1 + size n.
Proof. unfold size. cbn. simpl_list. rewrite repeat_length. cbn. omega. Qed.

Lemma Encode_Com_hasSize_ge1 (t : Com) :
  1 <= size t.
Proof. unfold size. destruct t; auto. unfold Encode_Heap. cbn. simpl_list. all: cbn; omega. Qed.

Lemma size_Com_singleton (t : Com) :
  size [t] = 2 + size t.
Proof. unfold size. destruct t; cbn; try omega. simpl_list. rewrite repeat_length. cbn. omega. Qed.

Lemma Encode_Pro_hasSize_ge1 (P : Pro) :
  1 <= size P.
Proof. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. Qed.

Lemma Encode_Pro_hasSize_ge_length (P : Pro) :
  length P <= Encode_list_size _ P.
Proof.
  induction P.
  - cbn. omega.
  - cbn. rewrite IHP. omega.
Qed.

Lemma Encode_Heap_hasSize_ge_length (H : Heap) :
  length H <= Encode_list_size _ H.
Proof.
  induction H.
  - cbn. omega.
  - cbn. rewrite IHlist. omega.
Qed.

(** ** JumpTarget *)

Module JumpTarget_steps_nice.

  Check App_ACom_steps.

  Print App_Commands_steps.

  Lemma App_Commands_steps_nice :
    { c | forall Q Q', App_Commands_steps Q Q' <=(c) size Q + size Q' }.
  Proof.
    eexists. intros. unfold App_Commands_steps.
    rewrite <- Nat.add_assoc. eapply dominatedWith_add_l.
    2:{ enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. }
    domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (App'_steps_nice _)). apply dominatedWith_solve.
      enough (size Q <= size Q + size Q') by auto. omega.
    - eapply dominatedWith_trans. unshelve eapply (proj2_sig (MoveValue_steps_nice' _ _)).
      1-2: setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
      hnf. setoid_rewrite encodeList_size_app.
      unfold sigPro, Pro, Encode_Prog. domWith_approx.
  Qed.

  Lemma App_ACom_steps_nice :
    { c | forall Q t, App_ACom_steps Q t <=(c) size Q }.
  Proof.
    eexists. intros. unfold App_ACom_steps. rewrite <- Nat.add_assoc. apply dominatedWith_add_l.
    2:{ setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. }
    unfold WriteValue_steps, App_Commands_steps.
    rewrite <- Nat.add_assoc. apply dominatedWith_add_l.
    2:{ setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. }
    domWith_approx.
    - hnf. rewrite size_ACom_singleton.
      instantiate (1 := 4). ring_simplify. enough (1 <= size Q) by omega.
      1: setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
    - setoid_rewrite Encode_list_hasSize. hnf. instantiate (1 := 1). ring_simplify. apply Encode_list_hasSize_ge1.
    - apply (proj2_sig (App'_steps_nice _)).
    - eapply dominatedWith_trans.
      unshelve eapply (proj2_sig (MoveValue_steps_nice' _ _)).
      1-2: setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
      hnf. setoid_rewrite encodeList_size_app.
      setoid_rewrite size_ACom_singleton. ring_simplify. instantiate (1 := 6).
      transitivity (2 * size Q + 4). 1:{ cbn [mult]. now rewrite Nat.add_0_r. } enough (2 * size Q + 4 <= 6 * size Q) by omega.
      enough (size Q + 2 <= 3 * size Q) by omega. enough (1 <= size Q) by nia.
      1: setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
  Qed.

  Lemma App_Com_steps_nice :
    { c | forall (Q : Pro) (t : Com), App_Com_steps Q t <=(c) size Q + size t }.
  Proof.
    eexists. intros. unfold App_Com_steps. rewrite <- !Nat.add_assoc. apply dominatedWith_add_l.
    2: { enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1. }
    ring_simplify. domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig Constr_nil_steps_nice).
      apply dominatedWith_solve. enough (1 <= size t /\ 1 <= size Q) by omega. split.
      + apply Encode_Com_hasSize_ge1.
      + setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
    - eapply dominatedWith_trans.
      + apply (proj2_sig (Constr_cons_steps_nice _)).
      + rewrite Nat.add_comm. apply dominatedWith_S'.
        * enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
        * apply dominatedWith_solve. enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
    - eapply dominatedWith_trans.
      + apply (proj2_sig App_Commands_steps_nice).
      + rewrite size_Com_singleton. ring_simplify. rewrite Nat.add_comm. eapply dominatedWith_add_l.
        * apply dominatedWith_refl. instantiate (1 := 1). omega.
        * enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
    - eapply dominatedWith_trans.
      + apply (proj2_sig (Reset_steps_nice _)).
      + rewrite Nat.add_comm. apply dominatedWith_add_l.
        * apply dominatedWith_solve. enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
        * enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
  Qed.

  Lemma JumpTarget_Step_steps_CaseCom_nice :
    { c | forall Q k t, JumpTargetTM.JumpTarget_Step_steps_CaseCom Q k t
                   <=(c)
                      match t with
                      | retT =>
                        match k with
                        | S _ => size Q
                        | 0 => 1
                        end
                      | lamT => size Q
                      | appT => size Q
                      | varT n => size Q + n
                      end }.
  Proof.
    eexists. intros. apply dominatedWith_match_Tok.
    - intros ->. apply (proj2_sig App_ACom_steps_nice).
    - intros ->. apply dominatedWith_add_l.
      + apply (proj2_sig App_ACom_steps_nice).
      + setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
    - intros ->. apply dominatedWith_match_nat.
      + intros ->. domWith_approx.
      + intros k' ->. apply dominatedWith_add_l.
        * apply (proj2_sig App_ACom_steps_nice).
        * setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
    - intros n ->. apply dominatedWith_add_l.
      + eapply dominatedWith_trans.
        * apply (proj2_sig App_Com_steps_nice).
        * rewrite size_Var. ring_simplify. rewrite Nat.add_comm. apply dominatedWith_add_l.
          -- apply dominatedWith_refl. constructor.
          -- enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
      + enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
  Qed.

  Lemma JumpTarget_Step_steps_CaseList_nice :
    { c | forall P Q k, JumpTargetTM.JumpTarget_Step_steps_CaseList P Q k
                   <=(c)
                      match P with
                      | t :: P' =>
                        match t with
                        | retT =>
                          match k with
                          | S _ => size Q
                          | 0 => 1
                          end
                        | lamT => size Q
                        | appT => size Q
                        | varT n => size Q + n
                        end
                      | nil => 1
                      end }.
  Proof.
    pose_nice JumpTarget_Step_steps_CaseCom_nice H c'.
    eexists. intros. apply dominatedWith_match_list.
    - intros ->. apply dominatedWith_solve. omega.
    - intros t P' ->. apply dominatedWith_add_l.
      + apply H.
      + destruct t.
        4: destruct k; [reflexivity| ].
        all: enough (1 <= size Q) by omega; setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
  Qed.

  Lemma JumpTarget_Step_steps_nice :
    { c | forall P Q k, JumpTargetTM.JumpTarget_Step_steps P Q k
                   <=(c)
                      match P with
                      | t :: P' =>
                        match t with
                        | retT =>
                          match k with
                          | S _ => size Q
                          | 0 => 1
                          end
                        | lamT => size Q
                        | appT => size Q
                        | varT n => size Q + n
                        end
                      | nil => 1
                      end }.
  Proof.
    pose_nice JumpTarget_Step_steps_CaseList_nice H c'.
    eexists. intros. unfold JumpTarget_Step_steps. specialize (H P Q k).
    rewrite <- Nat.add_assoc. apply dominatedWith_add_l.
    - apply dominatedWith_add.
      + apply dominatedWith_match_list.
        * intros ->. apply dominatedWith_const. omega.
        * intros t P' ->. destruct t.
          -- eapply dominatedWith_trans.
             ++ apply (proj2_sig (CaseList_steps_cons_nice _)).
             ++ rewrite size_Var. ring_simplify. rewrite Nat.add_comm. apply dominatedWith_add_l.
                ** apply dominatedWith_solve. enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
                ** enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
          -- eapply dominatedWith_trans. apply (proj2_sig (CaseList_steps_cons_nice _)).
             hnf. cbn. setoid_rewrite (size_ACom' appAT). enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
          -- eapply dominatedWith_trans. apply (proj2_sig (CaseList_steps_cons_nice _)).
             hnf. cbn. setoid_rewrite (size_ACom' lamAT). enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
          -- eapply dominatedWith_trans. apply (proj2_sig (CaseList_steps_cons_nice _)).
             hnf. cbn. setoid_rewrite (size_ACom' retAT).
             destruct k. omega.
             enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
      + apply H.
    - destruct P; [reflexivity| ]. destruct c.
      4: destruct k; [reflexivity| ].
      all: enough (1 <= size Q) by omega; setoid_rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1.
  Qed.

  Lemma JumpTarget_Loop_steps_nice :
    { c | forall P Q k, JumpTargetTM.JumpTarget_Loop_steps P Q k <=(c) size Q * size P * size k }.
  Proof.
    pose_nice JumpTarget_Step_steps_nice Hc_steps c_steps.
    exists (c_steps + 1). induction P as [ | t P' IH]; intros.
    - specialize (Hc_steps nil Q k).
      cbn [JumpTarget_Loop_steps]. hnf. ring_simplify. rewrite Hc_steps.
      setoid_rewrite Encode_list_hasSize. cbn.
      setoid_rewrite Encode_nat_hasSize. ring_simplify.
      setoid_rewrite <- Encode_list_hasSize_ge1. lia.
    - cbn [JumpTarget_Loop_steps].
      destruct t.
      + hnf. setoid_rewrite Hc_steps. unfold dominatedWith in IH. setoid_rewrite IH. ring_simplify.
        setoid_rewrite encodeList_size_app.
        setoid_rewrite size_Com_singleton. setoid_rewrite size_Var.
        setoid_rewrite Encode_list_hasSize; cbn [Encode_list_size].
        setoid_rewrite size_Var.
        setoid_rewrite Encode_nat_hasSize. ring_simplify. admit.
      + hnf. setoid_rewrite Hc_steps. unfold dominatedWith in IH. setoid_rewrite IH.
        setoid_rewrite encodeList_size_app.
        setoid_rewrite Encode_list_hasSize; cbn [Encode_list_size].
        setoid_rewrite (size_ACom' appAT).
        ring_simplify.
        setoid_rewrite <- Encode_list_hasSize.
        setoid_rewrite Encode_nat_hasSize. ring_simplify.
        rewrite <- !Nat.add_assoc. do 2 eapply plus_le_compat_l. ring_simplify.

        enough (size Q * (c_steps + size P' * k + size P') + size P' * (4 * c_steps * k + 4 * c_steps * size P' + 4 * k + 4) + 1 <=
                size Q * (3 * c_steps * k + 3 * c_steps + size P' * k + size P' + 3 * k + 3)).
        { ring_simplify in H. rewrite <- !Nat.mul_assoc in H. rewrite !(Nat.mul_comm (size Q)) in H. ring_simplify in H. rewrite <- H.
          ring_simplify. admit.
        }
        admit.
      + admit.
      + destruct k.
        * hnf. setoid_rewrite Hc_steps. ring_simplify.
          enough (c_steps <= c_steps * size Q * size (retT :: P') * size 0) as H by (rewrite <-H; nia).
          enough (1 <= size Q /\ 1 <= size (retT :: P') /\ 1 <= size 0) as (?&?&?) by nia. repeat split.
          -- setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
          -- setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
          -- setoid_rewrite Encode_nat_hasSize. reflexivity.
        * admit.
  Abort.

  (** Fabian's lemma *)
  Lemma JumpTarget_Step_steps_nice' :
    { c | forall P Q k, JumpTarget_Step_steps P Q k <=(c) hd 0 (map size P) + size Q + 1}.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig JumpTarget_Step_steps_nice).
    domWith_match.
    - cbn. apply dominatedWith_solve. enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
    - domWith_match; cbn.
      + apply dominatedWith_solve. enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
      + apply dominatedWith_solve. enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
      + domWith_match.
        * apply dominatedWith_solve. enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
        * apply dominatedWith_solve. enough (1 <= size Q) by omega. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
      + subst. apply dominatedWith_solve. enough (1 <= size Q /\ 2 + x0 <= size (varT x0)) by omega. split.
        * setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
        * now setoid_rewrite size_Var.
  Qed.

  (** Fabian's second lemma *)
  Lemma JumpTarget_Loop_steps_nice :
    { c | forall (P Q:Pro) (k:nat), JumpTarget_Loop_steps P Q k <=(c) (size Q + size P + length P + 1) * (length P + 1)}.
  Proof.
    pose_nice JumpTarget_Step_steps_nice H1 c1.
    evar (c:nat). exists c.
    intros P Q k. unfold dominatedWith.
    assert (c1 <= c) by shelve.
    induction P in Q,k|-*;cbn [JumpTarget_Loop_steps].
    - rewrite H1.
      cbn [hd map]. ring_simplify; nia.
    - destruct a;[..|destruct k].
      all:setoid_rewrite H1.
      all:try rewrite IHP.
      all:cbn [hd map length].
      all:unfold Encode_Prog, sigPro, Pro.
      all:repeat rewrite_sizes.
      all:rewrite H.
      1-3,5:assert (H':1<=c) by shelve;rewrite H' at 1.
      1-5:ring_simplify.
      (* We can now just check that every term is indeed bound *)
      1: setoid_rewrite size_Var.
      all: nia.
      Unshelve.
      instantiate (c := (max 1 c1)).
      all:eauto using Nat.le_max_r, Nat.le_max_l.
  Qed.

  Lemma JumpTarget_steps_nice :
    { c | forall P, JumpTarget_steps P <=(c) size P * size P}.
  Proof.
    Ltac sizePge1 := (lazymatch goal with [P : Pro |- _] => apply dominatedWith_solve; enough (1 <= size P) by nia; apply Encode_Pro_hasSize_ge1 end).
    eexists. intros. unfold JumpTarget_steps. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (Constr_nil_steps_nice)). sizePge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Constr_O_steps_nice)). sizePge1.
    - eapply dominatedWith_trans. apply (proj2_sig (JumpTarget_Loop_steps_nice)).
      setoid_rewrite Encode_list_hasSize. cbn. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
      + apply dominatedWith_solve. enough (|P| <= Encode_list_size _ P) by nia. apply Encode_Pro_hasSize_ge_length.
      + apply dominatedWith_solve. enough (|P| <= Encode_list_size _ P) by nia. apply Encode_Pro_hasSize_ge_length.
      + apply dominatedWith_solve. enough (|P| <= Encode_list_size _ P) by nia. apply Encode_Pro_hasSize_ge_length.
      + enough (1 <= Encode_list_size _ P) by nia. apply Encode_list_hasSize_ge1.
    - enough (1 <= size P) by nia; apply Encode_Pro_hasSize_ge1.
  Qed.

End JumpTarget_steps_nice.

Print Assumptions JumpTarget_steps_nice.JumpTarget_steps_nice.


From Undecidability Require Import LAM.TM.LookupTM.


(** ** LM Lookup *)


Lemma Encode_Clos_hasSize (g : HClos) :
  size g = fst g + Encode_list_size _ (snd g) + 1.
Proof.
  destruct g as (a,P); cbn.
  setoid_rewrite Encode_pair_hasSize; unfold Encode_pair_size.
  setoid_rewrite Encode_nat_hasSize.
  setoid_rewrite Encode_list_hasSize.
  omega.
Qed.

Lemma Encode_Clos_hasSize' (g : HClos) :
  size g = size (fst g) + Encode_list_size _ (snd g).
Proof.
  destruct g as (a,P); cbn.
  setoid_rewrite Encode_pair_hasSize; unfold Encode_pair_size.
  setoid_rewrite Encode_nat_hasSize.
  setoid_rewrite Encode_list_hasSize.
  omega.
Qed.

Lemma Encode_Clos_hasSize_ge1 (g : HClos) :
  1 <= size g.
Proof. rewrite Encode_Clos_hasSize. omega. Qed.

Lemma Encode_HEntr_hasSize_ge1 (e : HEntr) :
  1 <= size e.
Proof. setoid_rewrite Encode_option_hasSize. apply Encode_option_hasSize_ge1. Qed.

Lemma Encode_Heap_hasSize_ge1 (H : Heap) :
  1 <= size H.
Proof. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. Qed.


Module LM_Lookup_nice.

  Lemma Lookup_Step_steps_CaseNat_nice :
    { c | forall (n : nat) (e' : HClos * HAdd), LookupTM.Lookup_Step_steps_CaseNat n e' <=(c) size (fst e') + size (snd e') }.
  Proof.
    eexists. intros n (g,b). unfold LookupTM.Lookup_Step_steps_CaseNat.
    domWith_match; subst; cbn -[mult plus].
    - ring_simplify. rewrite Nat.add_comm. apply dominatedWith_add_l. 1: domWith_approx.
      + eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)). hnf. instantiate (1 := 1). ring_simplify.
        enough (1 <= size g) by omega. apply Encode_Clos_hasSize_ge1.
      + apply dominatedWith_const. enough (1 <= size g) by omega. apply Encode_Clos_hasSize_ge1.
      + eapply dominatedWith_trans. apply (proj2_sig (Translate_steps_nice _)).
        hnf. instantiate (1 := 1). ring_simplify.
        enough (1 <= size g /\ 1 <= size b) by omega. split. apply Encode_Clos_hasSize_ge1. apply Encode_nat_hasSize_ge1.
      + enough (1 <= size g) by omega. apply Encode_Clos_hasSize_ge1.
    - ring_simplify. rewrite Nat.add_comm. apply dominatedWith_add_l. 1: domWith_approx.
      + eapply dominatedWith_trans. apply (proj2_sig (CopyValue_steps_nice _)). hnf. instantiate (1 := 1). ring_simplify.
        enough (1 <= size g) by omega. apply Encode_Clos_hasSize_ge1.
      + eapply dominatedWith_trans. apply (proj2_sig (Translate_steps_nice _)).
        hnf. instantiate (1 := 1). ring_simplify.
        enough (1 <= size g /\ 1 <= size b) by omega. split. apply Encode_Clos_hasSize_ge1. apply Encode_nat_hasSize_ge1.
      + eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)). hnf. instantiate (1 := 1). ring_simplify.
        enough (1 <= size g) by omega. apply Encode_Clos_hasSize_ge1.
      + eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)). hnf. instantiate (1 := 1). ring_simplify.
        enough (1 <= size g /\ 1 <= size b) by omega. split. apply Encode_Clos_hasSize_ge1. apply Encode_nat_hasSize_ge1.
      + enough (1 <= size g) by omega. apply Encode_Clos_hasSize_ge1.
  Qed.

  Lemma Lookup_Step_steps_CaseOption_nice :
    { c | forall (n : nat) (e : HEntr), LookupTM.Lookup_Step_steps_CaseOption n e <=(c) size e }.
  Proof.
    eexists. intros. unfold LookupTM.Lookup_Step_steps_CaseOption. domWith_match; subst.
    - destruct x as (g,b). ring_simplify. rewrite Nat.add_comm. apply dominatedWith_add_l. 1: domWith_approx.
      + eapply dominatedWith_trans. apply (proj2_sig (CasePair_steps_nice _)).
        apply dominatedWith_solve. setoid_rewrite Encode_option_hasSize. cbn. setoid_rewrite Encode_pair_hasSize at 2. cbn.
        hnf. enough (size g + 1 <= size g + size b) by auto with arith. enough (1 <= size b) by omega. apply Encode_nat_hasSize_ge1.
      + apply dominatedWith_const. setoid_rewrite Encode_option_hasSize. cbn. omega.
      + eapply dominatedWith_trans. apply (proj2_sig Lookup_Step_steps_CaseNat_nice). cbn.
        apply dominatedWith_solve. setoid_rewrite Encode_option_hasSize. cbn. setoid_rewrite Encode_pair_hasSize at 2. cbn.
        hnf. enough (size g + 1 <= size g + size b) by auto with arith. enough (1 <= size b) by omega. apply Encode_nat_hasSize_ge1.
      + setoid_rewrite Encode_option_hasSize. cbn. omega.
    - apply dominatedWith_const. setoid_rewrite Encode_option_hasSize. cbn. omega.
  Qed.

  Lemma Lookup_Step_steps_Nth'_nice :
    { c | forall (H : list HEntr) (a n : nat),
        LookupTM.Lookup_Step_steps_Nth' H a n
        <=(c) match nth_error H a with
             | None => 1
             | Some e => size e
             end }.
  Proof.
    eexists. intros. unfold LookupTM.Lookup_Step_steps_Nth'. domWith_match.
    - apply dominatedWith_add_l.
      + apply (proj2_sig Lookup_Step_steps_CaseOption_nice).
      + apply Encode_HEntr_hasSize_ge1.
    - domWith_approx.
  Qed.

  Lemma Lookup_Step_steps_nice :
    { c | forall (H : Heap) (a n : nat), LookupTM.Lookup_Step_steps H a n <=(c) size H + size a }.
  Proof.
    eexists. intros. rewrite Encode_nat_hasSize. unfold Lookup_Step_steps. setoid_rewrite <- Nat.add_assoc. eapply dominatedWith_add_l.
    - domWith_approx.
      + eapply dominatedWith_trans. apply (proj2_sig (Nth'_steps_nice _)).
        rewrite Nat.add_comm. apply dominatedWith_add_l.
        * apply dominatedWith_solve. enough (size H + a <= size H + S a) by eauto. omega. (* walkaround some problem with typeclasses and [omega] *)
        * enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
      + eapply dominatedWith_trans. apply (proj2_sig Lookup_Step_steps_Nth'_nice). domWith_match.
        * apply dominatedWith_solve. enough (size x < size H) by omega.
          setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_el.
          eapply nth_error_In; eauto.
        * apply dominatedWith_solve. enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
    - enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
  Qed.

  (* We don't need to compute with this any more, since we have the upper bound *)
  Arguments Lookup_Step_steps : simpl never.

  (* How can we undo [Arguments : simpl never]? *)
  Lemma Lookup_steps_eq (H : Heap) (a : HAdd) (n : nat) :
    Lookup_steps H a n =
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Lookup_Step_steps H a n
      | S n' => 1 + Lookup_Step_steps H a n + Lookup_steps H b n'
      end
    | _ => Lookup_Step_steps H a n
    end.
  Proof. destruct n; reflexivity. Qed.

  (** The greatest address for [nth_error] that is encountered duing the execution of [lookup] *)
  Fixpoint heap_greatest_address (H : Heap) (a : HAdd) (n : nat) { struct n } : HAdd :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => a
      | S n' => max a (heap_greatest_address H b n')
      end
    | _ => a
    end.

  Lemma heap_greatest_address_eq (H : Heap) (a : HAdd) (n : nat) :
    heap_greatest_address H a n =
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => a
      | S n' => max a (heap_greatest_address H b n')
      end
    | _ => a
    end.
  Proof. destruct n; reflexivity. Qed.

  Lemma ge1_mul (a b : nat) :
    1 <= a -> 1 <= b -> 1 <= a * b.
  Proof. nia. Qed.

  Lemma Encode_nat_hasSize_max (a b : nat) :
    size (max a b) = max (size a) (size b).
  Proof. rewrite !Encode_nat_hasSize. nia. Qed.

  Lemma max_plus (a b c : nat) :
    max (c + a) (c + b) = c + max a b.
  Proof. lia. Qed.

  Lemma max_mult (a b c : nat) :
    c * max b c = max (c*a) (c*b).
  Proof. Abort.

  Lemma Lookup_steps_nice :
    { c | forall (H : Heap) (a : HAdd) (n : nat), Lookup_steps H a n <=(c) size n * (size H + size (heap_greatest_address H a n)) }.
  Proof.
    pose_nice Lookup_Step_steps_nice Hc_step c_step.
    exists (1 + c_step).
    intros. induction n as [ | n' IH] in H,a|-*.
    - rewrite Lookup_steps_eq. cbn.
      destruct (nth_error H a) as [ [ (g,b) | ] | ] eqn:E; cbn.
      + hnf. rewrite Hc_step. ring_simplify. rewrite !Encode_nat_hasSize. ring_simplify. nia.
      + hnf. rewrite Hc_step. ring_simplify. rewrite !Encode_nat_hasSize. ring_simplify. nia.
      + hnf. rewrite Hc_step. ring_simplify. rewrite !Encode_nat_hasSize. ring_simplify. nia.
    - rewrite Lookup_steps_eq. cbn -[mult plus].
      destruct (nth_error H a) as [ [ (g,b) | ] | ] eqn:E.
      + (* Recursion case *)
        hnf. unfold dominatedWith in IH. setoid_rewrite IH. rewrite Hc_step.
        enough (1 + c_step * (size H + size a) + (1 + c_step) * (size n' * (size H + size (heap_greatest_address H b n'))) <=
                (1 + c_step) * (size (S n') * (size H + size (Init.Nat.max a (heap_greatest_address H b n'))))) by auto.
        ring_simplify. rewrite !Encode_nat_hasSize. ring_simplify. nia.
      + hnf. rewrite Hc_step. rewrite !Encode_nat_hasSize. ring_simplify. nia.
      + hnf. rewrite Hc_step. rewrite !Encode_nat_hasSize. ring_simplify. nia.
  Qed.

  Lemma heap_greatest_address_invalid (H : Heap) (a : HAdd) (n : nat) :
    nth_error H a = None \/ nth_error H a = Some None ->
    heap_greatest_address H a n = a.
  Proof. rewrite heap_greatest_address_eq. now intros [-> | ->]. Qed.

  (* largest address in all of H *)
  Fixpoint heap_greatest_address2 (H:Heap) :=
    match H with
      [] => 0
    | Some (g,a) :: H => max a (heap_greatest_address2 H)
    | _ :: H => heap_greatest_address2 H
    end.

  Lemma heap_greatest_address_leq H a n :
    heap_greatest_address H a n <= max a (heap_greatest_address2 H).
  Proof.
    induction n in H,a|-*.
    all:rewrite heap_greatest_address_eq;cbn.
    -destruct nth_error as  [[[]| ]| ];eauto with arith.
    -destruct nth_error as  [[[g b]| ]| ] eqn:eq. 2,3:eauto with arith.
     rewrite IHn.
     assert (H':b <= heap_greatest_address2 H).
     { clear - eq.
      induction a in H,eq|-*;destruct H as [ | [[] | ]];inv eq;cbn. now eauto with arith.
      all:rewrite IHa;try eassumption. all: eauto with arith.
     }
     rewrite H'. repeat apply Nat.max_case_strong;eauto. 
  Qed.

  Section heap_global_greatest_address_Bound.

    (* Make sure that we just use the above lemmas for [max_list] *)
    Local Arguments max_list : simpl never.

    (** [heap_greatest_address] is bounded by the maximal occuring heap address (pointer) in the heap *)
    Definition heap_global_greatest_address_helper (e : HEntr) : nat :=
      match e with
      | Some (g, b) => b
      | None => 0
      end.

    Definition heap_global_greatest_address (H : Heap) :=
      max_list_map heap_global_greatest_address_helper H.

    Lemma heap_global_greatest_address_ge H g b :
      In (Some (g, b)) H ->
      b <= heap_global_greatest_address H.
    Proof.
      intros. unfold heap_global_greatest_address.
      pose proof max_list_map_ge heap_global_greatest_address_helper H0. cbn in *. auto.
    Qed.

    Lemma heap_greatest_address_bounded (H : Heap) (a : HAdd) (n : nat) :
      heap_greatest_address H a n <= max a (heap_global_greatest_address H).
    Proof.
      induction n as [ | n' IH] in a|-*; cbn in *.
      - destruct (nth_error H a) as [ [ (g',b) | ] | ] eqn:E; nia.
      - destruct (nth_error H a) as [ [ (g',b) | ] | ] eqn:E; try nia.
        assert (b <= heap_global_greatest_address H) as L by (eapply heap_global_greatest_address_ge; eapply nth_error_In; eauto).
        specialize (IH b). lia.
    Qed.


    (* The size of the list is an upper bound for [max_list_map]. (Actually, we could prove that this holds strictly) *)
    Lemma Encode_list_hasSize_ge_max (sigX X : Type) (cX : codable sigX X) (xs : list X) :
      max_list_map size xs <= Encode_list_size _ xs.
    Proof. apply max_list_map_lower_bound. intros x Hx. apply Nat.lt_le_incl. now eapply Encode_list_hasSize_el. Qed.


    Lemma heap_greatest_address_size (H : Heap) (a : HAdd) (n : nat) :
      heap_greatest_address H a n <= max (size a) (size H).
    Proof.
      rewrite heap_greatest_address_bounded.
      unfold heap_global_greatest_address.
      setoid_rewrite max_list_map_monotone.
      - setoid_rewrite Encode_list_hasSize_ge_max. setoid_rewrite Encode_list_hasSize. instantiate (1 := Encode_HEntr). rewrite Encode_nat_hasSize. nia.
      - intros [ [ g b ] | ]; cbn. 2: omega. setoid_rewrite Encode_option_hasSize; cbn. setoid_rewrite Encode_pair_hasSize. cbn. setoid_rewrite Encode_nat_hasSize. omega.
    Qed.

  End heap_global_greatest_address_Bound.


End LM_Lookup_nice.

Print Assumptions LM_Lookup_nice.Lookup_steps_nice.


From Undecidability Require Import LAM.TM.StepTM LAM.TM.HaltingProblem.
From Undecidability Require Import LAM.TM.SizeAnalysis.

Module LM.
  Import JumpTarget_steps_nice LM_Lookup_nice.

  (** Auxilliary machines *)

  Lemma TailRec_steps_nice :
    { c | forall (P : Pro) (a : HAdd), TailRec_steps P a <=(c) size P + size a }.
  Proof.
    eexists. intros. unfold TailRec_steps. domWith_match.
    - apply dominatedWith_add_l.
      + apply dominatedWith_const. unfold size. cbn. omega.
      + unfold size. cbn. omega.
    - subst. ring_simplify. rewrite Nat.add_comm. rewrite !Nat.add_assoc. do 2 rewrite <- Nat.add_assoc. apply dominatedWith_add_l.
      1: domWith_approx.
      + eapply dominatedWith_trans. apply (proj2_sig (Constr_pair_steps_nice _)). apply dominatedWith_add_r.
        * apply dominatedWith_solve. unfold sigHAdd. nia.
        * enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
      + eapply dominatedWith_trans. apply (proj2_sig (Constr_cons_steps_nice _)). apply dominatedWith_add_r.
        * apply dominatedWith_solve. setoid_rewrite Encode_pair_hasSize. cbn. setoid_rewrite Encode_list_hasSize. cbn. ring_simplify. unfold sigHAdd. nia.
        * enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
      + eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)).
        apply dominatedWith_add_r.
        * setoid_rewrite Encode_pair_hasSize. cbn. setoid_rewrite Encode_list_hasSize. cbn. ring_simplify.
          apply dominatedWith_solve.
          (* This is equivialent to [unfold sigHAdd]. *)
          progress enough (size a + size x + Encode_list_size Encode_Com xs + 1 <= size x + Encode_list_size Encode_Com xs + size a + 1) by auto. nia.
        * unfold size. cbn. omega.
      + unfold size. cbn. omega.
  Qed.

  Lemma ConsClos_steps_nice :
    { c | forall (Q : Pro) (a : HAdd), ConsClos_steps Q a <=(c) size Q + size a }.
  Proof.
    eexists. intros. unfold ConsClos_steps. rewrite <- !Nat.add_assoc. apply dominatedWith_add_l. 1:domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (Constr_pair_steps_nice _)). apply dominatedWith_solve. enough (1 <= size Q) by omega. apply Encode_Pro_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Constr_cons_steps_nice _)).
      eapply dominatedWith_add_r.
      + apply dominatedWith_solve. setoid_rewrite Encode_pair_hasSize. cbn. unfold sigHAdd. nia.
      + enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)).
      eapply dominatedWith_add_r.
      + apply dominatedWith_solve. setoid_rewrite Encode_pair_hasSize. cbn. unfold sigHAdd. nia.
      + enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)).
      eapply dominatedWith_add_r.
      + apply dominatedWith_solve. unfold sigHAdd. nia.
      + enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
    - enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
  Qed.


  (** LAM machine *)

  Lemma Step_lam_steps_JumpTarget_nice :
    { c | forall (P : Pro) (a : HAdd),
        Step_lam_steps_JumpTarget P a
        <=(c)
           match jumpTarget 0 [] P with
           | Some (Q', P') => size a + size P' + size Q'
           | None => 0
           end }.
  Proof.
    eexists. intros. unfold Step_lam_steps_JumpTarget. domWith_match.
    - destruct x as (Q',P'). ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
      + eapply dominatedWith_trans. apply (proj2_sig (TailRec_steps_nice)). apply dominatedWith_solve. nia.
      + eapply dominatedWith_trans. apply (proj2_sig (ConsClos_steps_nice)). apply dominatedWith_solve. nia.
      + enough (1 <= size P') by omega. apply Encode_Pro_hasSize_ge1.
    - domWith_approx.
  Qed.

  Lemma Step_lam_steps_nice' :
    { c | forall (P : Pro) (a : HAdd),
        Step_lam_steps P a
        <=(c)
           match jumpTarget 0 [] P with
           | Some (Q', P') => size a + size P * size P + size P' + size Q'
           | None => size P * size P
           end }.
  Proof.
    eexists. intros. unfold Step_lam_steps. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig JumpTarget_steps_nice). destruct jumpTarget as [(Q',P')| ]; apply dominatedWith_solve; nia.
    - eapply dominatedWith_trans. apply (proj2_sig Step_lam_steps_JumpTarget_nice). destruct jumpTarget as [(Q',P')| ]; apply dominatedWith_solve; nia.
    - destruct jumpTarget as [(Q',P')| ]; enough (1 <= size P) by nia; apply Encode_Pro_hasSize_ge1.
  Qed.

  (* maxi's lemma *)
  Lemma jumpTarget_size' (k : nat) (P Q Q' P' : Pro) :
    jumpTarget k Q P = Some (Q', P') ->
    size Q' + size P' <= size P + size Q /\
    size P' < size P.
  Proof.
    repeat setoid_rewrite Encode_list_hasSize.
    induction P as [ | c P IH] in Q,Q',P',k|-*; cbn [jumpTarget] in *.
    - congruence.
    - destruct c; cbn [jumpTarget]; intros.
      + modpon IH. rewrite IH; eauto. cbn [Encode_list_size]. rewrite size_Var. rewrite Encode_list_hasSize_app. cbn. rewrite size_Var. cbn. split; nia.
      + modpon IH. rewrite IH, IH0. rewrite Encode_list_hasSize_app. cbn. setoid_rewrite (size_ACom' appAT). cbn. repeat split; try nia.
      + modpon IH. rewrite IH, IH0. cbn [Encode_list_size]. rewrite Encode_list_hasSize_app. cbn [Encode_list_size].
        setoid_rewrite (size_ACom' lamAT). cbn [plus mult]. split; nia.
      + destruct k as [ | k'].
        -- inv H. cbn [Encode_list_size]. setoid_rewrite (size_ACom' retAT). repeat split; try nia.
        -- inv H. modpon IH. rewrite IH, IH0. rewrite Encode_list_hasSize_app. cbn [Encode_list_size]. setoid_rewrite (size_ACom' retAT). split; nia.
  Qed.

  Lemma jumpTarget_size (P : Pro) (Q' P' : Pro) :
    jumpTarget 0 [] P = Some (Q', P') ->
    size P' + size Q' <= size P + 1.
  Proof.
    intros. pose proof jumpTarget_size' H as [L1 L2]. setoid_rewrite (Encode_list_hasSize _ nil) in L1. cbn in *. nia.
  Qed.
 
  (* Fabian's lemma *)
  Lemma jumpTarget_size_fab (P : Pro) (Q' P' : Pro) :
    jumpTarget 0 [] P = Some (Q', P') ->
    size P' <= size P /\ size Q' <= size P.
  Proof.
    intros H.
    apply jumpTarget_eq in H. cbn in H. rewrite <- H.
    split.
    all:unfold Pro,sigPro,Encode_Prog in *.
    all:repeat rewrite encodeList_size_app_eq.
    all:repeat rewrite encodeList_size_cons.
    all:omega. 
  Qed.

  Lemma Step_lam_steps_nice :
    { c | forall (P : Pro) (a : HAdd), Step_lam_steps P a <=(c) size a + size P * size P }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Step_lam_steps_nice').
    domWith_match; rename H into E; [destruct x as (Q',P')| ].
    - apply dominatedWith_trans with (y := (size a + size P * size P + size P + 1)).
      { apply dominatedWith_solve. rewrite <- Nat.add_assoc. apply jumpTarget_size in E. rewrite E. omega. }
      domWith_approx. apply dominatedWith_solve. enough (1 <= size a) by nia. apply Encode_nat_hasSize_ge1.
    - apply dominatedWith_solve. omega.
  Qed.


  (** Put *)

  Lemma Put_steps_nice :
    { c | forall (H : Heap) (g : HClos) (b : HAdd), Put_steps H g b <=(c) size H + size g + size b }.
  Proof.
    eexists. intros. unfold Put_steps. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (Length_steps_nice _)). apply dominatedWith_solve.
      enough (size H <= size H + size g + size b) by auto. omega.
    - eapply dominatedWith_trans. apply (proj2_sig (Constr_nil_steps_nice)).
      apply dominatedWith_solve. enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Translate_steps_nice _)).
      apply dominatedWith_solve. enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Translate_steps_nice _)).
      apply dominatedWith_solve. enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Constr_pair_steps_nice _)).
      apply dominatedWith_solve. enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Constr_Some_steps_nice)).
      apply dominatedWith_solve. enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Constr_cons_steps_nice _)).
      setoid_rewrite Encode_option_hasSize. cbn. setoid_rewrite Encode_pair_hasSize at 1. cbn. setoid_rewrite Encode_nat_hasSize.
      ring_simplify. unfold Encode_pair_size. apply dominatedWith_add_r. apply dominatedWith_solve. omega. omega.
    - eapply dominatedWith_trans. apply (proj2_sig (App'_steps_nice _)).
      apply dominatedWith_solve. enough (size H <= size H + size g + size b) by auto. omega.
    - eapply dominatedWith_trans. apply (proj2_sig (MoveValue_steps_nice _ _)).
      setoid_rewrite Encode_list_hasSize. rewrite Encode_list_hasSize_app. cbn. setoid_rewrite Encode_option_hasSize. cbn. setoid_rewrite Encode_pair_hasSize at 1. cbn. ring_simplify. eapply dominatedWith_add_r. domWith_approx.
      + eapply dominatedWith_trans with (Encode_list_size Encode_HEntr H + size g + size b + 3).
        * apply dominatedWith_solve.
          transitivity (Encode_list_size Encode_HEntr H + 2 + (size g + size b + 1)).
          -- rewrite <- !Nat.add_assoc. apply Nat.le_sub_l.
          -- rewrite <- !Nat.add_assoc. ring_simplify. nia.
        * apply dominatedWith_add_r. apply dominatedWith_solve. omega. enough (1 <= Encode_list_size _ H) by omega. apply Encode_list_hasSize_ge1.
      + enough (1 <= Encode_list_size _ H) by omega. apply Encode_list_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)).
      setoid_rewrite Encode_option_hasSize. cbn. setoid_rewrite Encode_pair_hasSize at 1. cbn. setoid_rewrite Encode_nat_hasSize.
      ring_simplify. unfold Encode_pair_size. apply dominatedWith_add_r. apply dominatedWith_solve. omega. omega.
    - eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)).
      apply dominatedWith_solve. enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
    - enough (1 <= size H) by omega. apply Encode_Heap_hasSize_ge1.
  Qed.

  (** APP *)

  Lemma Step_app_steps_CaseList'_nice :
    { c | forall (g : HClos) (V' : list HClos) (H : Heap) (P : Pro) (a : HAdd),
        Step_app_steps_CaseList' g V' H P a
        <=(c)
           match V' with
           | [] => 0
           | (b,Q) :: _ => size a + size b + size g + size H + size P + size Q + size (length H)
           end }.
  Proof.
    eexists. intros. unfold Step_app_steps_CaseList'. domWith_match; subst. 1: now domWith_approx.
    destruct x as (b,Q). ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (CasePair_steps_nice _)).
      apply dominatedWith_solve. enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (TailRec_steps_nice)).
      apply dominatedWith_solve. enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)).
      apply dominatedWith_solve. enough (1 <= size b) by omega. apply Encode_nat_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Put_steps_nice)). apply dominatedWith_solve. nia.
    - eapply dominatedWith_trans. apply (proj2_sig (ConsClos_steps_nice)).
      apply dominatedWith_solve. enough (size Q + size (| H |) <= size a + size b + size g + size H + size P + size Q + size (| H |)) by auto. omega.
    - enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
  Qed.

  Lemma Step_app_steps_CaseList_nice :
    { c | forall (V : list HClos) (H : Heap) (P : Pro) (a : HAdd),
        Step_app_steps_CaseList V H P a
        <=(c)
           match V with
           | [] => 0
           | g :: V' => size a + size H + size P + size (length H) + size g + size V'
           end }.
  Proof.
    eexists. intros. unfold Step_app_steps_CaseList. domWith_match; subst; [now domWith_approx | rename x into g, xs into V'].
    ring_simplify. eapply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (CaseList_steps_nice _)).
      destruct V' as [ | e V'']; cbn.
      + apply dominatedWith_solve. enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
      + apply dominatedWith_solve. rewrite Encode_list_hasSize; cbn. omega.
    - eapply dominatedWith_trans. apply (proj2_sig Step_app_steps_CaseList'_nice).
      destruct V' as [ | (b,Q) V'']; cbn.
      + domWith_approx.
      + apply dominatedWith_solve. rewrite Encode_list_hasSize; cbn. setoid_rewrite (Encode_pair_hasSize _ _ (b,Q)); cbn.
        ring_simplify. enough (size a + size b + size g + size H + size P + size Q + size (| H |) <= size a + size g + size H + size P + size Q + size (| H |) + size b + Encode_list_size Encode_HClos V'' + 1) by auto. nia.
    - enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
  Qed.

  Lemma Step_app_steps_nice :
    { c | forall (V : list HClos) (H : Heap) (a : HAdd) (P : Pro), Step_app_steps V H a P <=(c) size a + size H + size P + size (length H) + size V }.
  Proof.
    eexists. intros. unfold Step_app_steps. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (CaseList_steps_nice _)). domWith_match; subst.
      + apply dominatedWith_solve. enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
      + apply dominatedWith_solve. rewrite Encode_list_hasSize; cbn. omega.
    - eapply dominatedWith_trans. apply (proj2_sig (Step_app_steps_CaseList_nice)). domWith_match; subst.
      + domWith_approx.
      + apply dominatedWith_solve. do 2 rewrite Encode_list_hasSize; cbn. omega.
    - enough (1 <= size a) by omega. apply Encode_nat_hasSize_ge1.
  Qed.

  (** VAR *)

  Lemma Step_var_steps_Lookup_nice :
    { c | forall (H : Heap) (a : HAdd) (n : Var),
        Step_var_steps_Lookup H a n
        <=(c) match lookup H a n with
             | Some g => size g
             | None => 0
             end }.
  Proof.
    eexists. intros. unfold Step_var_steps_Lookup. domWith_match; rename H0 into E.
    ring_simplify. apply dominatedWith_add_r. all: domWith_approx.
    - eapply dominatedWith_trans. eapply (proj2_sig (Constr_cons_steps_nice _)). apply dominatedWith_add_r. domWith_approx. apply Encode_Clos_hasSize_ge1.
    - eapply dominatedWith_trans. eapply (proj2_sig (Reset_steps_nice _)). apply dominatedWith_add_r. domWith_approx. apply Encode_Clos_hasSize_ge1.
    - apply Encode_Clos_hasSize_ge1.
  Qed.

  Lemma lookup_size (H : Heap) (a : HAdd) (n : Var) (g : HClos) :
    lookup H a n = Some g ->
    size g < size H.
  Proof.
    induction n as [ | n'] in a,n|-*; intros HEq; cbn in *.
    - destruct (nth_error H a) as [ [ (g',b) | ] | ] eqn:E; inv HEq.
      transitivity (size (Some (g, b))).
      + setoid_rewrite Encode_option_hasSize; cbn. setoid_rewrite Encode_pair_hasSize at 2; cbn. omega.
      + apply nth_error_In in E. setoid_rewrite Encode_list_hasSize. now apply Encode_list_hasSize_el.
    - destruct (nth_error H a) as [ [ (g',b) | ] | ] eqn:E; inv HEq. eauto.
  Qed.

  Lemma Step_var_steps_nice' :
    { c | forall (P : Pro) (H : Heap) (a : HAdd) (n : Var),
        Step_var_steps P H a n
        <=(c) size P + size a + size H + size n * (size H + size (heap_greatest_address H a n)) }.
  Proof.
    eexists. intros. unfold Step_var_steps. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig TailRec_steps_nice). apply dominatedWith_solve. nia.
    - eapply dominatedWith_trans. apply (proj2_sig Lookup_steps_nice). apply dominatedWith_solve. ring_simplify. enough (size n * size H + size n * size (heap_greatest_address H a n) <= size H * size n + size H + size (heap_greatest_address H a n) * size n + size P + size a) by auto. nia.
    - eapply dominatedWith_trans. apply (proj2_sig Step_var_steps_Lookup_nice). apply dominatedWith_solve.
      destruct lookup eqn:E.
      + enough (size h < size H) by nia. eapply lookup_size; eauto.
      + nia.
    - enough (1 <= size a) by nia. apply Encode_nat_hasSize_ge1.
  Qed.


  (** Step *)

  Lemma Step_steps_CaseCom_nice :
    { c | forall (a : HAdd) (t : Com) (P' : Pro) (V : list HClos) (H : Heap),
        Step_steps_CaseCom a t P' V H
        <=(c)
           match t with
           | varT n => size P' + size a + size H + size n * (size H + size (heap_greatest_address H a n)) (* TODO: Can we make this more nice? *)
           | appT => size a + size H + size P' + size (length H) + size V
           | lamT => size a + size P' * size P'
           | retT => 0
           end }.
  Proof.
    eexists. intros. unfold Step_steps_CaseCom. domWith_approx; subst.
    - eapply dominatedWith_trans. apply (proj2_sig Step_app_steps_nice). apply dominatedWith_solve. omega.
    - eapply dominatedWith_trans. apply (proj2_sig Step_lam_steps_nice). apply dominatedWith_solve. omega.
    - eapply dominatedWith_trans. apply (proj2_sig Step_var_steps_nice'). apply dominatedWith_solve. omega.
  Qed.

  Lemma heap_greatest_address_ge (H : Heap) (a : HAdd) (n : Var) :
    a <= heap_greatest_address H a n.
  Proof.
    intros. induction n as [ | n' IH] in H,a|-*; cbn in *.
    - destruct (nth_error H a) as [ [ (g,b) | ] | ] eqn:E; cbn; omega.
    - destruct (nth_error H a) as [ [ (g,b) | ] | ] eqn:E; cbn.
      + assert (heap_greatest_address H b n' <= a \/ a <= heap_greatest_address H b n') as [HO|HO] by omega.
        * rewrite max_l by assumption. omega.
        * rewrite max_r by assumption. assumption.
      + omega.
      + omega.
  Qed.

  Lemma size_length_heap (H : Heap) :
    size (length H) <= Encode_list_size _ H.
  Proof.
    induction H as [ | e H IH].
    - cbn. unfold size. cbn. omega.
    - cbn. setoid_rewrite <- IH. rewrite Encode_nat_hasSize.
      enough (S (length H) <= size (length H)) by omega.
      rewrite Encode_nat_hasSize. reflexivity.
  Qed.

  Lemma Encode_Heap_hasSize_ge_length (H : Heap) :
    length H <= Encode_list_size _ H.
  Proof.
    induction H as [ | e H IH].
    - cbn. unfold size. cbn. omega.
    - cbn. setoid_rewrite <- IH. omega.
  Qed.

  (* TODO: Apply nicer bound for [heap_greatest_address] here *)
  Lemma Step_steps_CaseList'_nice :
    { c | forall (a : HAdd) (P : Pro) (V : list HClos) (H : Heap),
        Step_steps_CaseList' a P V H
        <=(c)
           match P with
           | [] => 0
           | t :: P' => size a + size H + size V + size P' * size P' + size t * ( 1 +size H + Init.Nat.max a (heap_greatest_address2 H))
           end }.
  Proof.
    eexists. intros. unfold Step_steps_CaseList'. domWith_match. 1:{ apply dominatedWith_refl. constructor. } ring_simplify.
    
    unfold Pro. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply dominatedWith_const. constructor. apply dominatedWith_solve.
      setoid_rewrite Encode_list_hasSize. setoid_rewrite <- Encode_list_hasSize_ge1. lia.
    - eapply dominatedWith_trans. apply (proj2_sig Step_steps_CaseCom_nice). domWith_match.
      + subst. domWith_approx.
        * apply dominatedWith_solve. unfold Pro. nia.
        * apply dominatedWith_solve.
          rewrite size_length_heap. setoid_rewrite Encode_list_hasSize. nia.
      + subst. apply dominatedWith_solve. unfold Pro. nia.
      + apply dominatedWith_const. unfold HAdd. pose (Encode_nat_hasSize_ge1 a). nia. 
      + unfold Pro.
        unfold HAdd. rewrite !Encode_nat_hasSize,size_Var.
        rewrite (heap_greatest_address_leq H a x0).
        ring_simplify.
        assert (H':=Encode_Pro_hasSize_ge1 xs). 
        assert (H'':=Encode_Heap_hasSize_ge1 H).
        assert (Hmul:size xs <= size xs * size xs) by nia. unfold Pro,sigPro,Encode_Prog in *. setoid_rewrite Hmul at 1.
        domWith_approx.
    - enough (1 <= size a) by nia. apply Encode_nat_hasSize_ge1.
  Qed.

  Lemma Step_steps_CaseList_nice :
    { c | forall (T V : list HClos) (H : Heap),
        Step_steps_CaseList T V H
        <=(c)
           match T with
           | [] => 0
           | (a,P) :: _ => size a + size H + size V + size P * ( 1 + size H + Init.Nat.max a (heap_greatest_address2 H) + size P)
           end }.
  Proof.
    eexists. intros. unfold Step_steps_CaseList. domWith_match. 1: now domWith_approx. destruct x as (a,P); rename xs into T', H0 into E. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (CasePair_steps_nice _)). apply dominatedWith_solve.
      enough (1 <= size H) by nia. apply Encode_Heap_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (CaseList_steps_nice _)). apply dominatedWith_solve.
      destruct P as [ | t P'] .
      + enough (1 <= size a) by nia. apply Encode_nat_hasSize_ge1.
      + repeat setoid_rewrite Encode_list_hasSize. cbn. nia.
    - eapply dominatedWith_trans. apply (proj2_sig Step_steps_CaseList'_nice). apply dominatedWith_solve.
      destruct P as [ | t P'] .
      + enough (1 <= size a) by nia. apply Encode_nat_hasSize_ge1.
      + repeat setoid_rewrite Encode_list_hasSize. cbn. ring_simplify. nia.
    - enough (1 <= size a) by nia. apply Encode_nat_hasSize_ge1.
  Qed.

  Lemma Step_steps_nice :
    { c | forall (T V : list HClos) (H : Heap),
        Step_steps T V H
        <=(c)
           match T with
           | [] => 1
           | (a,P) :: _ => size a + size H + size V + size P * ( 1 + size H + Init.Nat.max a (heap_greatest_address2 H) + size P)
           end }.
  Proof.
    eexists. intros. unfold Step_steps. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig (CaseList_steps_nice _)). domWith_match; [now domWith_approx | ].
      destruct x as (a,P). setoid_rewrite Encode_pair_hasSize. cbn. apply dominatedWith_solve.
      unfold sigHAdd.
      enough (1 <= size P) by nia. apply Encode_Pro_hasSize_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig (Step_steps_CaseList_nice)). domWith_match; [now domWith_approx | ].
      destruct x as (a,P). apply dominatedWith_solve. omega.
    - destruct T. omega. destruct h as (a,P). enough (1 <= size a) by nia. apply Encode_nat_hasSize_ge1.
  Qed.

  (** Loop *)

  (* TODO *)

End LM.

Print Assumptions LM.Step_steps_nice.
