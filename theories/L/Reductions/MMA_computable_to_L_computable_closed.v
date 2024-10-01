(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Minsky Machine combinability (MMA_computable) implies L computability (L_computable_closed)
*)

Require Import List PeanoNat Lia Relations Transitive_Closure.
Import ListNotations.

From Undecidability.MinskyMachines Require Import MMA Util.MMA_facts mma_defs.

From Undecidability.L Require Import L Util.term_facts.
From Undecidability.L Require Util.L_facts Prelim.ARS.
Import L_facts (step).

From Undecidability.Shared Require Import Libs.DLW.Code.sss simulation.

Require Import Undecidability.L.Reductions.MMA_HALTING_to_HaltLclosed.

Require Import ssreflect.

Unset Implicit Arguments.

Set Default Goal Selector "!".

#[local] Notation lams k M := (Nat.iter k lam M).
#[local] Notation apps M Ns := (fold_left app Ns M).

Fixpoint fin_seq n : list (Fin.t n) :=
  match n with
  | 0 => []
  | S n => Fin.F1 :: map Fin.FS (fin_seq n)
  end.

Opaque Vector.to_list Fin.L.

(* apps (enc_regs (Vector.const 0 (1 + k + n))) (Vector.to_list (Vector.map (fun x => enc_replace (Fin.L n (Fin.FS x))) (rev_vec_seq k)))*)
Definition enc_set_state k n : term :=
  apps (enc_regs (Vector.const 0 (1 + k + n)))
  (map (fun '(x, i) => app (enc_replace (Fin.FS (Fin.L n x))) (var i)) (combine (fin_seq k) (rev (seq 0 k)))).

Opaque enc_replace Vector.to_list.

Lemma substs_enc_set_state k n (v : Vector.t nat k) :
  clos_refl_trans _ step
    (substs 0 (rev (map nat_enc (VectorDef.to_list v))) (enc_set_state k n))
    (enc_regs (Vector.append (Vector.cons nat 0 k v) (Vector.const 0 n))) .
Proof.
  have : clos_refl_trans _ step
    (substs 0 (rev (map nat_enc (VectorDef.to_list v))) (enc_set_state k n))
    (enc_regs (fold_left (fun w '(x, c) => Vector.replace w (Fin.FS (Fin.L n x)) c) (combine (fin_seq k) (Vector.to_list v)) (Vector.const 0 (1 + k + n)))).
  { rewrite /enc_set_state.
  move: (Vector.const 0 (1 + k + n))=> cs.
  rewrite substs_apps substs_closed; first by apply: enc_regs_closed.
    have ->: forall xs, map (substs 0 (rev (map nat_enc (VectorDef.to_list v))))
      (map (fun '(x, i) => app (enc_replace (Fin.L n (Fin.FS x))) (var i))
      (combine xs (rev (seq 0 k)))) =
      map (fun '(x, c) => app (enc_replace (Fin.L n (Fin.FS x))) (nat_enc c))
      (combine xs (Vector.to_list v)).
  { elim: v; first by move=> ? [|??].
    move=> c k' v IH ? [|x xs]; first done.
    have ->: seq 0 (S k') = seq 0 (k' + 1).
    { congr seq. lia. }
    rewrite seq_app rev_app_distr Vector.to_list_cons /=. congr cons.
    - rewrite substs_closed; first by apply: enc_replace_closed.
      congr app. rewrite app_nth2 length_rev length_map Vector.length_to_list; first done.
      by rewrite Nat.sub_diag.
    - rewrite -IH. apply: map_ext_in=> s /in_map_iff [[y j]] [<-].
      move=> /(@in_combine_r (Fin.t _) nat) /in_rev.
      rewrite rev_involutive=> /in_seq ? /=.
      rewrite !substs_closed; [by apply: enc_replace_closed..|].
      congr app. rewrite app_nth1; last done.
      rewrite length_rev length_map Vector.length_to_list. lia. }
  
  move: (fin_seq k)=> xs.
  move: (Vector.to_list v)=> c's.
  elim: xs c's cs {v}.
  - move=> *. by apply: rt_refl.
  - move=> x xs IH [|c' c's].
    + move=> *. by apply: rt_refl.
    + move=> cs /=. apply: rt_trans.
      { apply: rt_steps_apps_r. apply: eval_rt_steps. apply: enc_replace_spec. by apply: eval_nat_enc. }
      by apply: IH. }
  congr clos_refl_trans. congr enc_regs.
  rewrite [RHS](@Vector.eta _ (k + n)) [LHS](@Vector.eta _ (k + n)).
  congr (@Vector.cons _ _ (k + n)); rewrite /=.
  - elim: (fin_seq k) (Vector.to_list v) (Vector.const 0 (k + n)); first done.
    by move=> ?? IH [|??] ?; [|apply: IH].
  - apply /Vector.eq_nth_iff=> x ? <-.
    pattern x. apply: Fin.case_L_R'=> {}x.
    + rewrite Vector.nth_append_L.
      have : forall x c, In (x, c) (combine (fin_seq k) (Vector.to_list v)) -> Vector.nth v x = c.
      { elim: v; first done.
        move=> > IH {}x c /=. rewrite Vector.to_list_cons /=.
        move=> [[??]|]; first by subst.
        rewrite combine_map_l.
        move=> /in_map_iff [[??]] [[??]] /IH ?. by subst. }
      have : In (x, Vector.nth v x) (combine (fin_seq k) (Vector.to_list v)).
      { elim: v x; first by apply: Fin.case0.
        move=> > IH x.
        pattern x. apply: Fin.caseS'; first by left.
        move=> {}x. rewrite Vector.to_list_cons /=. right.
        rewrite combine_map_l. apply /in_map_iff. by eexists (_, _). }
      rewrite -Vector.append_const.
      move: (VectorDef.const 0 k).
      elim /rev_ind: (combine (fin_seq k) (Vector.to_list v)); first done.
      move=> [y j] ? IH ? /in_app_iff H'.
      move=> H. rewrite fold_left_app /=.
      rewrite [fold_left _ _ _](@Vector.eta _ (k + n)) /=.
      have [?|?] := Fin.eq_dec x y.
      * subst. rewrite Vector.nth_replace_eq.
        rewrite (H y j); last done.
        apply /in_app_iff. right. by left.
      * rewrite Vector.nth_replace_neq; first by move=> /Fin.L_inj.
        apply: IH=> *.
        ** by move: H' => [|[[/(@eq_sym (Fin.t k))]|]].
        ** apply: H. apply /in_app_iff. by left.
    + rewrite Vector.nth_append_R Vector.const_nth -Vector.append_const.
      elim: (fin_seq k) (Vector.to_list v) (VectorDef.const 0 k).
      * move=> /= *. by rewrite Vector.nth_append_R Vector.const_nth.
      * move=> ?? IH [|??] ? /=; first by rewrite Vector.nth_append_R Vector.const_nth.
        by rewrite Vector.replace_append_L IH.
Qed.

Lemma subst_enc_set_state k n m u : subst (enc_set_state k n) (k + m) u = enc_set_state k n.
Proof.
  rewrite /enc_set_state subst_apps enc_regs_closed.
  congr fold_left. rewrite map_map.
  apply: map_ext_in=> - [x i].
  rewrite /= enc_replace_closed.
  move=> /(@in_combine_r (Fin.t k) nat) /in_rev.
  rewrite rev_involutive.
  move=> /in_seq ?.
  by have /Nat.eqb_neq -> : i <> k + m by lia.
Qed.

Opaque enc_run pi enc_set_state enc_nth.

Lemma enc_init_spec {k n} (P : list (MM.mm_instr (Fin.t (1 + k + n)))) (v : Vector.t nat k) :
  clos_refl_trans _ step
    (Vector.fold_left (fun (s : term) c => app s (nat_enc c))
      (lams k (apps (enc_run P) [pi P (addr P 1); enc_set_state k n; enc_run P; enc_nth (@Fin.F1 (k + n))])) v)
    (apps (enc_run P) [pi P (addr P 1); enc_regs (Vector.append (Vector.cons nat 0 k v) (Vector.const 0 n)); enc_run P; enc_nth (@Fin.F1 (k + n))]).
Proof.
  rewrite Vector.to_list_fold_left.
  have ->: forall cs t, fold_left (fun s c => app s (nat_enc c)) cs t = apps t (map nat_enc cs).
  { elim; first done.
    move=> > IH ? /=. by rewrite IH. }
  apply: rt_trans.
  { apply: steps_apps_lams.
    - by rewrite length_map Vector.length_to_list.
    - apply /Forall_map /Forall_forall=> *. by apply: eval_nat_enc.
    - apply /Forall_map /Forall_forall=> *. by apply: nat_enc_closed. }
  rewrite substs_apps /=.
  apply: rt_trans.
  { do 2 apply: rt_steps_app_r. apply: rt_steps_app_l.
    by apply: substs_enc_set_state. }
  rewrite !substs_closed; [by auto using enc_run_closed, pi_addr_closed, enc_nth_closed..|].
  by apply: rt_refl.
Qed.

Theorem MMA_computable_to_L_computable_closed {k} (R : Vector.t nat k -> nat -> Prop) :
  MMA_computable R -> L_computable_closed R.
Proof.
  unfold MMA_computable, L_computable_closed.
  move=> [n [P HP]].
  (* \c1...\ck. run pi_1 ((0...0) (set 1 c1) .. (set k ck)) run (\c'1...\c'n.c'1) *)
  exists (lams k (apps (enc_run P) [pi P (addr P 1); enc_set_state k n; enc_run P; enc_nth (@Fin.F1 (k + n))])).
  split.
  - intros u ?.
    rewrite subst_lams subst_apps !map_cons subst_enc_set_state.
    by rewrite !enc_run_closed pi_addr_closed enc_nth_closed.
  - move=> v. split.
    + move=> m. rewrite HP. split.
      * intros [c [v' [H1 H2]]].
        apply /L_facts.eval_iff. split; last by (case: (m); eexists).
        apply /ARS.star_clos_rt_iff. apply: rt_trans.
        { by apply: enc_init_spec. }
        move=> /sss_compute_iff in H1.
        have := @clos_refl_trans_transport _ _
        (sss_step (@mma_sss ((1 + k + n))) (1, P))
        L_facts.step
        (sync P)
        (@sss_step_transport _ P)
        (1, Vector.append (Vector.cons nat 0 k v) (Vector.const 0 n))
        _ (c, Vector.cons nat m (k + n) v') eq_refl H1.
        move=> [t [-> Ht]].
        apply: rt_trans.
        { apply: rt_steps_app_r. by eassumption. }
        apply: rt_trans.
        { apply: rt_steps_app_r. by apply: enc_run_spec_out_code. }
        apply: eval_rt_steps. by apply: enc_nth_spec.
      * move=> /eval_rt_steps_eval => /(_ _ (enc_init_spec _ _)).
        move: (Vector.append _ _)=> {}v /[dup] /eval_steps_stuck H'.
        have /(@Acc_clos_trans term) := @terminating_Acc _ _ L_facts.uniform_confluence _ H'.
        have [i Hi] : exists i, 1 = i by eexists.
        rewrite [in addr P 1]Hi [in (1, v)]Hi.
        move E: (apps _ _) => t H.
        elim: H i v E {H' Hi}.
        move=> {}t IH1 IH2 i v ?. subst t.
        have [[[j w]]|] := sss_step_or_stuck (@mma_sss_total_ni _) (i, v) 1 P.
        ** move=> /[dup] Hvw /enc_run_spec /=.
           move=> /(@t_steps_app_r _ _ (enc_nth (@Fin.F1 (k + n)))).
           move=> /[dup] /(@clos_trans_clos_refl_trans term) /eval_rt_steps_eval H' + /H'.
           move=> /clos_trans_flip /IH2 /(_ _ _ eq_refl) /[apply].
           move=> [c] [v'] [??]. exists c, v'. split; last done.
           apply: sss_compute_trans; last by eassumption.
           apply /sss_compute_iff.
           by apply: rt_step.
        ** move=> /[dup] /(out_code_iff (@mma_sss_total_ni _)) /enc_run_spec_out_code H.
           move=> /[dup] /(out_code_iff (@mma_sss_total_ni _)) H''.
           move=> /stuck_sss_step_transport => /(_ _ eq_refl) [t] H'.
           move: H=> /(rt_steps_app_r _ _ (enc_nth (@Fin.F1 (k + n)))).
           move=> /eval_rt_steps_eval /[apply].
           have /L_facts.eval_iff [+ [??]] := enc_nth_spec (@Fin.F1 (k + n)) v.
           move=> /ARS.star_clos_rt_iff /eval_rt_steps_eval /[apply].
           have := eval_nat_enc (Vector.nth v Fin.F1).
           move=> /L_facts.eval_iff /L_facts.eval_unique + /L_facts.eval_iff => /[apply].
           move=> /nat_enc_inj <-.
           exists i, (snd (@Vector.splitat _ 1 (k + n) v)).
           split; last done.
           apply /sss_compute_iff.
           rewrite (Vector.eta v).
           by apply: rt_refl.
    + move=> o /eval_rt_steps_eval => /(_ _ (enc_init_spec _ _)).
      move: (Vector.append _ _)=> {}v /[dup] /eval_steps_stuck H'.
      have /(@Acc_clos_trans term) := @terminating_Acc _ _ L_facts.uniform_confluence _ H'.
      move: (1) => i.
      move E: (apps _ _) => t H.
      elim: H i v E {H'}.
      move=> {}t IH1 IH2 i v ?. subst t.
      have [[[j w]]|] := sss_step_or_stuck (@mma_sss_total_ni _) (i, v) 1 P.
      * move=> /enc_run_spec /=.
        move=> /(@t_steps_app_r _ _ (enc_nth (@Fin.F1 (k + n)))).
        move=> /[dup] /(@clos_trans_clos_refl_trans term) /eval_rt_steps_eval H' + /H'.
        by move=> /clos_trans_flip /IH2 /(_ _ _ eq_refl) /[apply].
      * move=> /[dup] /(out_code_iff (@mma_sss_total_ni _)) /enc_run_spec_out_code H.
        move=> /stuck_sss_step_transport => /(_ _ eq_refl) [t] H'.
        move: H=> /(rt_steps_app_r _ _ (enc_nth (@Fin.F1 (k + n)))).
        move=> /eval_rt_steps_eval /[apply].
        have /L_facts.eval_iff [+ [??]] := enc_nth_spec (@Fin.F1 (k + n)) v.
        move=> /ARS.star_clos_rt_iff /eval_rt_steps_eval /[apply].
        have := eval_nat_enc (Vector.nth v Fin.F1).
        move=> /L_facts.eval_iff /L_facts.eval_unique + /L_facts.eval_iff => /[apply] <-.
        by eexists.
Qed.
