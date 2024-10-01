(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Reduction from:
    Alternate Minsky Machine with n Registers Halting (MMA_HALTING n)
  to:
    Halting Problem for Weak Call-by-value lambda-Calculus (HaltLclosed)
*)

Require Import List PeanoNat Lia Relations Transitive_Closure.
Import ListNotations.

From Undecidability.MinskyMachines Require Import MMA Util.MMA_facts mma_defs.

From Undecidability.L Require Import L Util.term_facts.
From Undecidability.L Require Util.L_facts Prelim.ARS.
Import L_facts (step).

From Undecidability.Shared Require Import Libs.DLW.Code.sss simulation.

Require Import ssreflect.

Unset Implicit Arguments.

Set Default Goal Selector "!".

(* general facts *)

Lemma vec_pos_nth {X : Type} {n} {v : Vector.t X n} {i} :
  vec.vec_pos v i = Vector.nth v i.
Proof.
  elim: v i; first by apply: Fin.case0.
  move=> ?? v IH i.
  pattern i. by apply: (Fin.caseS' i).
Qed.

Lemma vec_change_replace {X : Type} {n} (v : Vector.t X n) i x :
  vec.vec_change v i x = Vector.replace v i x.
Proof.
  elim: v i; first by apply: Fin.case0.
  move=> ?? v IH i.
  pattern i. apply: (Fin.caseS' i); first done.
  move=> ?. by congr Vector.cons.
Qed.

Lemma nth_order_map : forall (X Y : Type) (f : X -> Y) (n : nat) (v : Vector.t X n) (i : nat) (H : i < n),
  Vector.nth_order (Vector.map f v) H = f (Vector.nth_order v H).
Proof.
  move=> X Y f n. elim; first by lia.
  move=> x {}n v IH [|i] H /=; first done.
  by apply: IH.
Qed.

Lemma nth_order_nth {X : Type} {n} (v : Vector.t X n) i {k} (H : k < n) :
  proj1_sig (Fin.to_nat i) = k -> Vector.nth_order v H = VectorDef.nth v i.
Proof.
  elim: v k i H.
  - move=> ?. by apply: Fin.case0.
  - move=> x {}n v IH [|k] i /=.
    + pattern i; apply: (Fin.caseS' i); first done.
      move=> i' /=. case: (Fin.to_nat i')=> /=. lia.
    + move=> ?. pattern i; apply: (Fin.caseS' i); first done.
      move=> i' /=. move E: (Fin.to_nat i') => [m Hm] /= [?].
      apply: IH. by rewrite E.
Qed.

Lemma vec_In_nil {X : Type} {x} : Vector.In x (Vector.nil X) -> False.
Proof.
  intros H. by inversion H.
Qed.

Lemma vec_In_replace {X : Type} {n} {v : Vector.t X n} {i x y} :
  Vector.In y (Vector.replace v i x) -> y = x \/ Vector.In y v.
Proof.
  elim: v i x.
  - by apply: Fin.case0.
  - move=> x {}n v IH /= i x'.
    pattern i. apply: (Fin.caseS' i).
    + move=> /= /Vector.In_cons_iff [<-|?]; first by left.
      right. by constructor.
    + move=> /= j /Vector.In_cons_iff [<-|/IH [?|?]].
      * right. by constructor.
      * by left.
      * right. by constructor.
Qed.

Lemma vec_In_map {X Y : Type} {n} {f : X -> Y} {v : Vector.t X n} {y} :
  Vector.In y (Vector.map f v) -> exists x, y = f x /\ Vector.In x v.
Proof.
  elim: v.
  - by move=> /vec_In_nil.
  - move=> x {}n v IH /= /Vector.In_cons_iff [<-|/IH].
    + eexists. split; first done. by constructor.
    + move=> [? [-> ?]].
      eexists. split; first done. by constructor.
Qed.

Lemma clos_t_rt_t {A : Type} {R : relation A} (x y z : A) :
  clos_trans A R x y -> clos_refl_trans A R y z -> clos_trans A R x z.
Proof.
  move=> H /clos_rt_rtn1_iff H'. elim: H' H; by eauto using clos_trans.
Qed.

Lemma map_nth' {X Y : Type} {f : X -> Y} {l i} {d} d' : i < length l -> nth i (map f l) d = f (nth i l d').
Proof.
  move=> H. rewrite (nth_indep _ _ (f d')); first by rewrite length_map.
  by apply: map_nth.
Qed.

Lemma combine_map_l {A B C} (f : A -> B) (l : list A) (r : list C) :
  combine (map f l) r = map (fun '(x, y) => (f x, y)) (combine l r).
Proof.
  elim: l r; first done.
  move=> > IH [|? r]; first done.
  move=> /=. by rewrite IH.
Qed.

Lemma clos_trans_flip {X : Type} {R : X -> X -> Prop} {x y} : clos_trans _ R x y ->
  clos_trans _ (fun y x => R x y) y x.
Proof. by elim; eauto using clos_trans. Qed.

#[local] Notation lams k M := (Nat.iter k lam M).
#[local] Notation apps M Ns := (fold_left app Ns M).

Section MMA_HALTING_to_HaltLclosed.

Opaque Nat.add Nat.sub.

Context {num_regs : nat}. (* number of registers - 1 *)
Notation N := (S num_regs).
Context (P : list (MM.mm_instr (Fin.t N))). (* program *)

#[local] Hint Rewrite subst_apps : subst.

Lemma eval_lams_S n s : eval (lams (S n) s) (lams (S n) s).
Proof.
  by constructor.
Qed.

#[local] Hint Resolve eval_lams_S : core.

Opaque Nat.iter.

(* remap machine addresses to 0 .. n (n + 1 => 0) *)
Definition addr i :=
  match i - length P with
  | 0 => i
  | S i => 0
  end.

Lemma addr_spec_in_code {l instr r} :
  P = l ++ instr :: r ->
  addr (S (length l)) = S (length l).
Proof.
  rewrite /addr=> ->. rewrite length_app /=.
  by have ->: S (length l) - (length l + S (length r)) = 0 by lia.
Qed.

Lemma addr_spec_out_code {i} : i < 1 \/ S (length P) <= i -> addr i = 0.
Proof.
  rewrite /addr => - [?|?].
  - have ->: i = 0 by lia.
    by case: (length P).
  - by have ->: i - length P = S (i - length P - 1) by lia.
Qed.

Definition pi i := lams (S (length P)) (var i).

Lemma eval_pi i : eval (pi i) (pi i).
Proof.
  by rewrite /pi.
Qed.

Lemma pi_addr_closed i : closed (pi (addr i)).
Proof.
  move=> k u. rewrite /pi subst_lams /=.
  have /Nat.eqb_neq ->: addr i <> S (length P + k); last done.
  rewrite /addr.
  case E: (i - length P) => [|]; lia.
Qed.

#[local] Hint Resolve eval_pi : core.
#[local] Hint Rewrite pi_addr_closed : subst.

Lemma apps_pi_spec {i} ts t :
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  length ts = S (length P) ->
  eval (nth i (rev ts) (var 0)) t ->
  eval (apps (pi i) ts) t.
Proof.
  move=> ?? Hts Ht. rewrite /pi -Hts.
  apply: eval_apps_lams; [done..|].
  rewrite /= (nth_indep _ _ (var 0)); last done.
  suff : i >= length (rev ts) -> False by lia.
  move=> ?. rewrite nth_overflow in Ht; first done.
  by inversion Ht.
Qed.

Opaque addr pi.

Lemma nat_enc_closed n : closed (nat_enc n).
Proof.
  elim: n; first done.
  move=> n IH u k /=. by rewrite IH.
Qed.

Lemma eval_nat_enc n : eval (nat_enc n) (nat_enc n).
Proof.
  by case: n; constructor.
Qed.

#[local] Hint Resolve eval_nat_enc : core.
#[local] Hint Rewrite nat_enc_closed : subst.

Lemma nat_enc_inj n m : nat_enc n = nat_enc m -> n = m.
Proof.
  elim: n m.
  - by case.
  - move=> n IH [|m] /=; first done.
    by move=> [/IH] <-.
Qed.

(* encode register values *)
(* \f.f c1 ... cN *)
Definition enc_regs (regs : Vector.t nat N) := lam (apps (var 0) (Vector.to_list (Vector.map nat_enc regs))).

Lemma eval_enc_regs ts : eval (enc_regs ts) (enc_regs ts).
Proof.
  by constructor.
Qed.

Lemma enc_regs_closed v : closed (enc_regs v).
Proof.
  rewrite /enc_regs. move=> k u.
  rewrite /= subst_apps /=.
  rewrite Vector.to_list_map map_map.
  congr lam. congr fold_left.
  apply: map_ext=> ?. by rewrite nat_enc_closed.
Qed.

#[local] Hint Resolve eval_enc_regs : core.
#[local] Hint Rewrite enc_regs_closed : subst.

Lemma enc_regs_spec v s t :
  eval (substs 0 (rev (Vector.to_list (Vector.map nat_enc v))) s) t ->
  eval (app (enc_regs v) (lams N s)) t.
Proof.
  move=> H. econstructor; [constructor|done|].
  rewrite subst_apps /=. apply: eval_apps_lams.
  - by rewrite length_map Vector.length_to_list.
  - apply /Forall_map. apply /Vector.to_list_Forall.
    apply /Vector.Forall_map.
    apply /Vector.Forall_nth=> y. rewrite nat_enc_closed.
    by apply: eval_nat_enc.
  - apply /Forall_map. apply /Vector.to_list_Forall.
    apply /Vector.Forall_map.
    apply /Vector.Forall_nth=> y. rewrite nat_enc_closed.
    by apply: nat_enc_closed.
  - move: H. congr eval. congr substs. congr rev.
    rewrite -Vector.to_list_map Vector.map_map.
    congr Vector.to_list. apply: Vector.map_ext.
    move=> c. by rewrite nat_enc_closed.
Qed.

Opaque enc_regs.

Definition nat_succ := lam (lam (lam (app (var 0) (var 2)))).

Lemma nat_succ_closed : closed nat_succ.
Proof.
  done.
Qed.

#[local] Hint Rewrite nat_succ_closed : subst.

Lemma nat_succ_spec t c : eval t (nat_enc c) -> eval (app nat_succ t) (nat_enc (S c)).
Proof.
  rewrite /nat_succ. move=> H.
  econstructor; [constructor|eassumption|].
  rewrite /=. by constructor.
Qed.

Opaque nat_succ.

(* just use of_list seq ? *)
Fixpoint rev_vec_seq n : Vector.t nat n :=
  match n with
  | 0 => Vector.nil _
  | S n => Vector.cons _ n _ (rev_vec_seq n)
  end.

Lemma rev_vec_seq_S n : rev_vec_seq (S n) = Vector.cons _ n _ (rev_vec_seq n).
Proof.
  done.
Qed.

Lemma vec_In_rev_seq n i : Vector.In i (rev_vec_seq n) -> i < n.
Proof.
  elim: n.
  - by move=> /vec_In_nil.
  - move=> n IH. rewrite rev_vec_seq_S.
    move=> /Vector.In_cons_iff [->|/IH]; lia.
Qed.

Opaque rev_vec_seq.

Lemma vec_nth_rev_seq n i : VectorDef.nth (rev_vec_seq n) i = n - 1 - proj1_sig (Fin.to_nat i).
Proof.
  elim: n i.
  - by apply: Fin.case0.
  - move=> n IH i.
    pattern i. apply: (Fin.caseS' i).
    + rewrite rev_vec_seq_S /=. lia.
    + move=> {}i /=. rewrite rev_vec_seq_S /= IH.
      move: (Fin.to_nat i) => [m Hm] /=. lia.
Qed.

(* get nth vector element *)
Definition enc_nth (x : Fin.t N) : term :=
  (* \c1 .. cN.cx *)
  lams N (var (N - 1 - proj1_sig (Fin.to_nat x))).

Lemma enc_nth_closed x : closed (enc_nth x).
Proof.
  move=> k u. rewrite /= subst_lams /=.
  by have /Nat.eqb_neq ->: N - 1 - proj1_sig (Fin.to_nat x) <> N + k by lia.
Qed.

Lemma enc_nth_spec x v : eval (app (enc_regs v) (enc_nth x)) (nat_enc (Vector.nth v x)).
Proof.
  apply: enc_regs_spec.
  move Ex: (Fin.to_nat x) => [n Hn] /=.
  rewrite /= rev_nth Vector.length_to_list; first lia.
  rewrite -Vector.to_list_nth_order; [|lia].
  move=> Hm. rewrite nth_order_map.
  rewrite -(Fin.of_nat_to_nat_inv x) Ex /=.
  rewrite (@nth_order_nth _ _ _ (Fin.of_nat_lt Hn)) ?Fin.to_nat_of_nat /=; first lia.
  by apply: eval_nat_enc.
Qed.

#[local] Hint Resolve enc_nth_spec : core.
#[local] Hint Rewrite enc_nth_closed : subst.
Opaque enc_nth.

(* set nth vector element *)
Definition enc_replace (x : Fin.t N) : term :=
  (* \c.\c1 .. cN.\f.f c1 .. c .. cN *)
  lam (lams N (lam (apps (var 0) (map var (Vector.to_list (Vector.replace (Vector.map S (rev_vec_seq N)) x (N + 1))))))).

Lemma enc_replace_closed x : closed (enc_replace x).
Proof.
  move=> k u. rewrite /= subst_lams /= subst_apps /=.
  rewrite /enc_replace.
  rewrite map_map -!Vector.to_list_map.
  congr lam. congr Nat.iter. congr lam. congr fold_left.
  congr Vector.to_list. apply: Vector.map_ext_in => n /= /vec_In_replace H.
  have /Nat.eqb_neq ->: n <> S (S (num_regs + S k)); last done.
  move: H => [->|]; first by lia.
  move=> /vec_In_map [?] [->] /vec_In_rev_seq. lia.
Qed.

Lemma enc_replace_spec x v c t :
  eval t (nat_enc c) ->
  eval (app (enc_regs v) (app (enc_replace x) t)) (enc_regs (Vector.replace v x c)).
Proof.
  move=> Hc. apply: rt_steps_eval_eval.
  - apply: rt_steps_app_l. apply: eval_rt_steps_subst. by eassumption.
  - rewrite subst_lams.
    apply: enc_regs_spec.
    rewrite /= subst_apps substs_apps. apply: eval_lam.
    rewrite /=. congr lam. congr fold_left.
    rewrite !map_map.
    rewrite -!Vector.to_list_map.
    congr Vector.to_list.
    apply /Vector.eq_nth_iff=> i ? <-.
    rewrite !(Vector.nth_map _ _ _ _ eq_refl) /=.
    have [?|?] := Fin.eq_dec i x.
    + subst i. rewrite !Vector.nth_replace_eq.
      have /Nat.eqb_eq ->: S (num_regs + 1) = S (S (num_regs + 0)) by lia.
      rewrite substs_closed; last done.
      by apply: nat_enc_closed.
    + rewrite !Vector.nth_replace_neq; [done..|].
      rewrite (Vector.nth_map _ _ _ _ eq_refl).
      rewrite vec_nth_rev_seq /=.
      have /Nat.eqb_neq -> /=: N - 1 - proj1_sig (Fin.to_nat i) <> S (num_regs + 0) by lia.
      move Ei: (Fin.to_nat i) => [n Hn] /=.
      rewrite rev_nth Vector.length_to_list; first lia.
      rewrite -Vector.to_list_nth_order; [|lia].
      move=> ?. rewrite nth_order_map. congr nat_enc.
      apply: nth_order_nth. rewrite Ei /=. lia.
Qed.

#[local] Hint Resolve enc_replace_spec : core.
#[local] Hint Rewrite enc_replace_closed : subst.
Opaque enc_replace.

Definition enc_instr '(i, instr) : term :=
  match instr with
  | MM.mm_inc x =>
      (* \cs.(\cs'.\f.f (pi (S i)) cs') (inc x cs) *)
      lam (app (lam (lam (apps (var 0) [pi (addr (S i)); var 1]))) (app (var 0) (app (enc_replace x) (app nat_succ (app (var 0) (enc_nth x))))))
  | MM.mm_dec x j =>
      (* \cs.(nth x cs) (\f. f (pi (S i)) cs) (\c.(\c'.\f. f (pi j) c') (replace x cs c)) *)
      lam (apps (var 0) [enc_nth x;
        lam (apps (var 0) [pi (addr (S i)); var 1]);
        lam (app (lam (lam (apps (var 0) [pi (addr j); var 1]))) (app (var 1) (app (enc_replace x) (var 0))))])
  end.

Lemma enc_instr_closed o : closed (enc_instr o).
Proof.
  move=> k u. case: o=> i [instr|instr x] /=; by autorewrite with subst.
Qed.

Lemma eval_enc_instr o : eval (enc_instr o) (enc_instr o).
Proof.
  move: o => [] ? []; by constructor.
Qed.

#[local] Hint Resolve eval_enc_instr : core.
#[local] Hint Rewrite enc_instr_closed : subst.

Definition enc_recurse :=
  (* \i.\cs.\run.run i cs run *)
  lam (lam (lam (apps (var 0) [var 2; var 1; var 0]))).

Lemma enc_recurse_closed : closed enc_recurse.
Proof.
  done.
Qed.

Lemma eval_enc_recurse : eval enc_recurse enc_recurse.
Proof.
  by constructor.
Qed.

#[local] Hint Resolve eval_enc_recurse : core.
#[local] Hint Rewrite enc_recurse_closed : subst.

(* \cs.\f.\run.cs *)
Definition enc_halt := lam (lam (lam (var 2))).
(* \i.i (halt :: P) *)
Definition enc_step := lam (apps (var 0) (rev (enc_halt :: map enc_instr (combine (seq 1 (length P)) P)))).

Lemma enc_halt_closed : closed enc_halt.
Proof.
  done.
Qed.

Lemma eval_enc_halt : eval enc_halt enc_halt.
Proof.
  by constructor.
Qed.

Lemma enc_halt_spec cs :
  clos_refl_trans _ step
  (apps enc_halt [enc_regs cs; enc_recurse; lam (lam (apps enc_step [var 1; var 0; enc_recurse]))])
  (enc_regs cs).
Proof.
  rewrite /enc_halt /=.
  apply: rt_trans.
  { do 2 apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { apply: rt_steps_app_r. rewrite /=. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { rewrite /=. apply: eval_rt_steps_subst. by constructor. }
  autorewrite with subst. by apply: rt_refl.
Qed.

#[local] Hint Resolve eval_enc_halt : core.
#[local] Hint Rewrite enc_halt_closed : subst.

Lemma map_subst_map_enc_instr k t l : map (fun u => subst u k t) (map enc_instr l) = map enc_instr l.
Proof.
  rewrite map_map. apply: map_ext=> ?. by rewrite enc_instr_closed.
Qed.

Lemma enc_step_closed : closed enc_step.
Proof.
  rewrite /enc_step. move=> k u /=. rewrite subst_apps /=.
  rewrite map_app map_rev map_subst_map_enc_instr /=.
  by autorewrite with subst.
Qed.

Lemma enc_step_spec l instr r cs :
  P = l ++ instr :: r ->
  clos_refl_trans term step
    (apps enc_step [pi (addr (S (length l))); enc_regs cs])
    (app (enc_instr (S (length l), instr)) (enc_regs cs)).
Proof.
  move=> HP.
  apply: rt_trans.
  { rewrite /= /enc_step. apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { rewrite /= subst_apps /=. apply: rt_steps_app_r.
    autorewrite with subst.
    rewrite map_app map_rev map_subst_map_enc_instr /=.
    apply: eval_rt_steps. apply: apps_pi_spec.
    - apply /Forall_app. split.
      + by apply /Forall_rev /Forall_map /Forall_forall=> *.
      + constructor; by autorewrite with subst.
    - apply /Forall_app. split.
      + apply /Forall_rev /Forall_map /Forall_forall=> * ??. by autorewrite with subst.
      + constructor; by autorewrite with subst.
    - rewrite length_app length_rev length_map length_combine length_seq /=. lia.
    - rewrite rev_app_distr rev_involutive (addr_spec_in_code HP) /=.
      rewrite (map_nth' (0, MM.mm_inc Fin.F1)).
      { rewrite length_combine length_seq HP length_app /=. lia. }
      rewrite combine_nth; first by rewrite length_seq.
      rewrite seq_nth.
      { rewrite HP length_app /=. lia. }
      have ->: nth (length l) P (INCₐ Fin.F1) = instr; last done.
      { by rewrite HP app_nth2 ?Nat.sub_diag. } }
  by apply: rt_refl.
Qed.

Lemma enc_step_0_spec :
  clos_refl_trans term step (app enc_step (pi 0)) enc_halt.
Proof.
  rewrite /enc_step.
  apply: rt_trans.
  { by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { rewrite /= subst_apps map_app map_rev map_subst_map_enc_instr /=.
    apply: eval_rt_steps. apply: apps_pi_spec.
    - apply /Forall_app. split.
      + by apply /Forall_rev /Forall_map /Forall_forall=> *.
      + constructor; by autorewrite with subst.
    - apply /Forall_app. split.
      + apply /Forall_rev /Forall_map /Forall_forall=> * ??. by autorewrite with subst.
      + constructor; by autorewrite with subst.
    - rewrite length_app length_rev length_map length_combine length_seq /=. lia.
    - by rewrite rev_app_distr rev_involutive /=. }
  by apply: rt_refl.
Qed.

#[local] Hint Rewrite enc_step_closed : subst.
Opaque enc_recurse enc_halt enc_step.

Lemma mma_step_sim (instr : MM.mm_instr (Fin.t N)) (p q : mm_state N) :
  mma_sss instr p q ->
  clos_refl_trans _ step
    (apps (enc_instr (fst p, instr)) [enc_regs (snd p); enc_recurse])
    (apps enc_recurse [pi (addr (fst q)); enc_regs (snd q)]).
Proof.
  case.
  - (* INC *)
    move=> i x v /=. rewrite vec_change_replace vec_pos_nth.
    apply: rt_trans.
    { apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
    apply: rt_trans.
    { apply: rt_steps_app_r. rewrite /=. apply: rt_steps_app_l.
      autorewrite with subst. apply: eval_rt_steps.
      apply: enc_replace_spec. apply: nat_succ_spec. by apply: enc_nth_spec. }
    apply: rt_trans.
    { apply: rt_steps_app_r. autorewrite with subst. by apply: eval_rt_steps_subst. }
    apply: rt_trans.
    { rewrite /=. by apply: eval_rt_steps_subst. }
    rewrite /=. autorewrite with subst. by apply: rt_refl.
  - (* DEC *)
    move=> i x j v. rewrite vec_pos_nth /==> Hx.
    apply: rt_trans.
    { apply: rt_steps_app_r.
      apply: rt_trans.
      { by apply: eval_rt_steps_subst. }
      apply: rt_trans.
      { rewrite /=. autorewrite with subst. do 2 apply: rt_steps_app_r. by apply: eval_rt_steps. }
      rewrite Hx /=. apply: rt_trans.
      { apply: rt_steps_app_r. apply: rt_step. by constructor. }
      apply: rt_step. rewrite /=. by constructor. }
    apply: rt_trans.
    { rewrite /=. autorewrite with subst. by apply: eval_rt_steps_subst. }
    rewrite /=. autorewrite with subst. by apply: rt_refl.
  - (* JUMP *)
    move=> i x j v c. rewrite vec_pos_nth vec_change_replace /==> Hx.
    apply: rt_trans.
    { apply: rt_steps_app_r.
      apply: rt_trans.
      { by apply: eval_rt_steps_subst. }
      apply: rt_trans.
      { rewrite /=. autorewrite with subst. do 2 apply: rt_steps_app_r. by apply: eval_rt_steps. }
      rewrite Hx /=. apply: rt_trans.
      { apply: rt_steps_app_r. apply: rt_step. by constructor. }
      apply: rt_step. rewrite /=. by constructor. }
    apply: rt_trans.
    { rewrite /=. autorewrite with subst. apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
    apply: rt_trans.
    { rewrite /=. autorewrite with subst. apply: rt_steps_app_r. apply: rt_steps_app_l.
      apply: eval_rt_steps. by apply: enc_replace_spec. }
    apply: rt_trans.
    { apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
    apply: rt_trans.
    { rewrite /=. autorewrite with subst. by apply: eval_rt_steps_subst. }
    rewrite /=. autorewrite with subst. by apply: rt_refl.
Qed.

(* \i.\cs.step i cs recurse *)
Definition enc_run := lam (lam (apps enc_step [var 1; var 0; enc_recurse])).

Lemma enc_run_closed : closed enc_run.
Proof.
  rewrite /enc_run. move=> k u /=. by autorewrite with subst.
Qed.

Lemma eval_enc_run : eval enc_run enc_run.
Proof.
  by constructor.
Qed.

#[local] Hint Rewrite enc_run_closed : subst.
#[local] Hint Resolve eval_enc_run : core.

Lemma enc_recurse_spec p :
  clos_refl_trans term step
    (apps enc_recurse [pi (addr (fst p)); enc_regs (snd p); enc_run])
    (apps enc_run [pi (addr (fst p)); enc_regs (snd p); enc_run]).
Proof.
  apply: rt_trans.
  { apply: rt_steps_app_r. apply: rt_steps_app_r. apply: rt_step. by apply: step_app'. }
  apply: rt_trans.
  { apply: rt_steps_app_r. apply: rt_step. rewrite /=. by apply: step_app'. }
  apply: rt_trans.
  { apply: rt_step. rewrite /=. by apply: step_app'. }
  rewrite /=. autorewrite with subst. by apply: rt_refl.
Qed.

Opaque enc_recurse.

Lemma t_steps_enc_run_enc_step i cs :
  clos_trans term step
    (apps enc_run [pi (addr i); enc_regs cs])
    (apps enc_step [pi (addr i); enc_regs cs; lam (lam (lam (apps (var 0) [var 2; var 1; var 0])))]).
Proof.
  apply: t_trans.
  { apply: t_steps_app_r. apply: t_step. apply: step_app'. by apply: eval_pi. }
  apply: clos_t_rt_t.
  { rewrite /=. apply: t_step. by apply: step_app'. }
  rewrite /=. autorewrite with subst. by apply: rt_refl.
Qed.

Opaque enc_instr.

Lemma enc_run_spec (p q : mm_state N) : @sss_step _ _ (@mma_sss N) (1, P) p q ->
  clos_trans term step
    (apps enc_run [pi (addr (fst p)); enc_regs (snd p); enc_run])
    (apps enc_run [pi (addr (fst q)); enc_regs (snd q); enc_run]).
Proof.
  move=> [k [l [instr [r [cs]]]]].
  move=> [[??]] [?]. subst k p.
  move=> /mma_step_sim Hpq. apply: clos_t_rt_t.
  { rewrite /=. apply: t_steps_app_r. by apply: t_steps_enc_run_enc_step. }
  apply: rt_trans.
  { apply: rt_steps_app_r. apply: rt_steps_app_r. rewrite /=.
    apply: enc_step_spec. by eassumption. }
  apply: rt_trans.
  { apply: rt_steps_app_r. by eassumption. }
  by apply: enc_recurse_spec.
Qed.

Lemma enc_run_spec_out_code (p : mm_state N) : fst p < 1 \/ S (length P) <= fst p ->
  clos_refl_trans _ step (apps enc_run [pi (addr (fst p)); enc_regs (snd p); enc_run]) (enc_regs (snd p)).
Proof.
  move=> Hp. rewrite /enc_run.
  apply: rt_trans.
  { apply: rt_steps_app_r. apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { apply: rt_steps_app_r. rewrite /=. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { apply: rt_steps_app_r. rewrite /=. autorewrite with subst.
    rewrite (addr_spec_out_code Hp). do 2 apply: rt_steps_app_r. by apply: enc_step_0_spec. }
  by apply: enc_halt_spec.
Qed.

Definition sync p t := t = apps enc_run [pi (addr (fst p)); enc_regs (snd p); enc_run].

Lemma sss_step_transport p q s :
  sss_step (@mma_sss N) (1, P) p q ->
  sync p s  ->
  exists t, clos_trans term step s t /\ sync q t.
Proof.
  move=> /enc_run_spec H ->.
  by exists (apps enc_run [pi (addr (fst q)); enc_regs (snd q); enc_run]).
Qed.

Lemma stuck_sss_step_transport p s :
  stuck (sss_step (@mma_sss N) (1, P)) p ->
  sync p s -> terminates step s.
Proof.
  move=> /(out_code_iff (@mma_sss_total_ni _)) Hp ->.
  exists (enc_regs (snd p)). split.
  - by apply: enc_run_spec_out_code.
  - move=> t. intros H. by inversion H.
Qed.

Opaque enc_run.

Lemma closed_apps_enc_run i cs : closed (apps enc_run [pi (addr i); enc_regs cs; enc_run]).
Proof.
  move=> k u. rewrite subst_apps /=. by autorewrite with subst.
Qed.

End MMA_HALTING_to_HaltLclosed.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction n : @MMA_HALTING n ⪯ HaltLclosed.
Proof.
  destruct n as [|n].
  { unshelve eexists.
    - intros _. now exists (lam (var 0)).
    - intros [[|??] st].
      + split.
        * intros _. exists (lam (var 0)). by constructor.
        * intros _. unfold MMA_HALTING, sss_terminates. exists (1, st).
          unfold sss_output, sss_compute. split.
          ** exists 0. now apply in_sss_steps_0.
          ** now right.
      + now destruct m as [x|x ?]; pattern x; apply Fin.case0. }
  unshelve eexists.
  - intros [P v]. exists (apps (enc_run P) [pi P (addr P 1); enc_regs v; enc_run P]).
    apply closed_apps_enc_run.
  - intros [P v]. split.
    + intros ?%(sss_terminates_iff (@mma_sss_total_ni _)).
      destruct (@terminates_transport _ _
        (sss_step (@mma_sss (S n)) (1, P))
        L_facts.step
        (sync P)
        (@sss_step_transport _ P)
        (@stuck_sss_step_transport _ P)
        (1, v) _ eq_refl H) as [t [H1t H2t]].
      exists t. cbn. eapply steps_stuck_eval; [|assumption..].
      apply closed_apps_enc_run.
    + intros [t Ht%eval_steps_stuck]. cbn in Ht.
      apply (sss_terminates_iff (@mma_sss_total_ni _)).
      apply (@terminates_reflection _ _
        (sss_step (@mma_sss (S n)) (1, P))
        L_facts.step
        (sync P)
        L_facts.uniform_confluence
        (@sss_step_transport _ P)
        (fun p => sss_step_or_stuck (@mma_sss_total_ni _) p 1 P)
        (1, v) _ eq_refl Ht).
Qed.
