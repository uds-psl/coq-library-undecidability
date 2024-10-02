(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  If a relation R is MMA_computable then it is MMA_mon_computable,
  where the first counter never decreases.
*)

From Undecidability Require Import TM.TM.
From Undecidability.MinskyMachines Require Import MM MMA MMA.mma_defs Util.MMA_computable Util.MMA_facts.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Undecidability.Shared.simulation.

Require Import List PeanoNat Lia Relations.
Import ListNotations.

Require Import ssreflect.

Module Sim := simulation.

Set Default Goal Selector "!".

#[local] Notation "P // s ~~> t" := (sss_output (@mma_sss _) P s t).
#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).

Definition NonZero {n} (a : Fin.t (S n)) :=
  if a is Fin.F1 then False else True.

(* MMA computability with a non-decreasing first counter value *)
Definition MMA_mon_computable {k} (R : Vector.t nat k -> nat -> Prop) :=
  exists n : nat, exists P : list (mm_instr (Fin.t (S (k + n)))),
    Forall (fun instr => if instr is DEC c _ then NonZero c else True) P /\
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c (v' : Vector.t nat (k + n)), (1, P) // (1, Vector.append (0 ## v) (Vector.const 0 n)) ~~> (c, m ## v')).

(* alternative characterization *)
Lemma MMA_mon_computable_iff {k} (R : Vector.t nat k -> nat -> Prop) :
  MMA_mon_computable R <->
  (exists n : nat, exists P : list (mm_instr (Fin.t (S (k + n)))),
    Forall (fun instr => if instr is DEC c _ then NonZero c else True) P /\
    (forall v m, R v m -> exists c v', (1, P) // (1, Vector.append (0 ## v) (Vector.const 0 n)) ~~> (c, m ## v')) /\
    (forall v, sss.sss_terminates (@mma_sss _) (1, P) (1, Vector.append (0 ## v) (Vector.const 0 n)) -> exists m, R v m)).
Proof.
  split.
  - move=> [n] [P] [H1P H2P]. exists n, P. split; [done|split].
    + by move=> ?? /H2P.
    + move=> v [[c' v']]. rewrite (Vector.eta v') => HP.
      exists (Vector.hd v'). apply /H2P.
      do 2 eexists. eassumption.
  - move=> [n] [P] [H1P [H2P H3P]]. exists n, P. split; [done|split].
    + apply: H2P.
    + move=> [c] [v'] Hm.
      have /H3P [m' Hm'] : sss_terminates (mma_sss (n:=S (k + n))) (1, P) (1, Vector.append (0 ## v) (Vector.const 0 n)).
      { eexists. eassumption. }
      suff : m' = m by move=> <-.
      move: Hm' Hm => /H2P [?] [?] /(sss_output_fun (@mma_sss_fun _)) /[apply].
      by move=> /pair_equal_spec [_] /Vector.cons_inj [].
Qed.

(* generic auxiliary facts *)
Module Facts.

Lemma vec_append_const (c : nat) n m : Vector.append (Vector.const c n) (Vector.const c m) = Vector.const c (n + m).
Proof.
  elim: n. { done. }
  by move=> ? /= ->.
Qed.

Lemma vec_app_eq {T : Type} {n m} {v : Vector.t T n} {w : Vector.t T m} : Vector.append v w = vec_app v w.
Proof.
  elim: v. { by rewrite vec_app_nil. }
  move=> > /= ->. by rewrite vec_app_cons.
Qed.

Lemma vec_append_splitat {X n m} (v : Vector.t X (n + m)) : v = Vector.append (fst (Vector.splitat _ v)) (snd (Vector.splitat _ v)).
Proof.
  apply: Vector.append_splitat.
  by case: (Vector.splitat n v).
Qed.

Lemma vec_append_inj {X n m} {v v' : Vector.t X n} {w w' : Vector.t X m} :
  Vector.append v w = Vector.append v' w' -> v = v' /\ w = w'.
Proof.
  move=> /(f_equal (Vector.splitat _)).
  rewrite !Vector.splitat_append. by move=> [<- <-].
Qed.

End Facts.
Import Facts.

Module MMA_MMA_mon.

Section FixedMMA.
Context {k k' : nat}.

#[local] Notation num_counters := ((1 + k) + k').
#[local] Notation num_counters' := ((1 + k) + (k' + 1)).

Context {P : list (mm_instr (pos num_counters))}.

(* auxiliary result counter *)
#[local] Notation F1' := (pos_right (1 + k) (pos_right k' Fin.F1)).

Definition shift_counter (X : pos num_counters) : pos num_counters' :=
  match pos_both _ _ X with
  | inl Fin.F1 => F1'
  | inl Y => pos_left _ Y
  | inr Y => pos_right _ (pos_left _ Y)
  end.

Definition shift_addr (p : nat) :=
  match p with
  | 0 =>  S (length P)
  | S p' =>
    match (S (length P)) - p' with
    | 0 => S (length P)
    | _ => p
    end
  end.

Definition shift_instr (instr : mm_instr (pos num_counters)) : mm_instr (pos num_counters') :=
  match instr with
  | INC X => INC (shift_counter X)
  | DEC X p => DEC (shift_counter X) (shift_addr p)
  end.

(* same as P, but F1' instead of F1 and move F1' to F1 when finished *)
Definition P' : list (mm_instr (pos num_counters')) :=
  map shift_instr P ++ [INC F1'; DEC F1' (4 + length P); INC Fin.F1; DEC F1' (3 + length P)].

Lemma length_P' : length P' = 4 + length P.
Proof.
  rewrite /P' length_app length_map /=. lia.
Qed.

Lemma P'_mon : Forall (fun instr => if instr is DEC c _ then NonZero c else True) P'.
Proof.
  rewrite /P'. apply /Forall_app. split.
  - apply /Forall_map /Forall_forall => - []; [done|].
    move=> X ? _ /=. pattern X. apply: Fin.caseS'; [done|].
    move=> {}X. rewrite /shift_counter /=.
    by case: (pos_both k k' X).
  - by do ? constructor.
Qed.

Lemma config_eqE2 (n n' i j a : nat) (v : Vector.t nat n) (w : Vector.t nat n') st : (i, Vector.append (a ## v) w) = (j, st) ->
  i = j /\ a = Vector.hd (fst (Vector.splitat _ st)) /\ v = Vector.tl ((fst (Vector.splitat _ st))) /\ w = snd (Vector.splitat _ st).
Proof.
  move=> /pair_equal_spec [->].
  move=> /(f_equal (Vector.splitat _)).
  rewrite Vector.splitat_append.
  move: (Vector.splitat _ st) => [a'v' w'].
  rewrite (Vector.eta a'v').
  by move=> /pair_equal_spec [/Vector.cons_inj] [-> ->] ->.
Qed.

#[local] Opaque Nat.sub.

Lemma shift_addr_range i : 1 <= i < S (S (length P)) -> shift_addr i = i.
Proof.
  move: i => [|i] ? /=; [lia|].
  by have -> : S (length P) - i = S (length P - i) by lia.
Qed.

Lemma in_mma_sss_dec_0' n (i i' : nat) (x : pos n) p (v v' : vec nat n) :
  i' = 1 + i ->
  v' = v ->
  vec_pos v x = 0 ->
  mma_sss (DEC x p) (i, v) (i', v').
Proof. move=> -> ->. by constructor. Qed.

Lemma in_mma_sss_dec_1' n u (i i' : nat) (x : pos n) p (v v' : vec nat n) :
  i' = p ->
  v' = vec_change v x u ->
  vec_pos v x = S u ->
  mma_sss (DEC x p) (i, v) (i', v').
Proof. move=> -> ->. by constructor. Qed.

Lemma in_mma_sss_inc' n (i i' : nat) (x : pos n) (v v' : vec nat n) :
  i' = 1 + i ->
  v' = vec_change v x (S (vec_pos v x)) ->
  mma_sss (INC x) (i, v) (i', v').
Proof. move=> -> ->. by constructor. Qed.

Lemma vec_pos_shift_counter x a v w :
  vec_pos (0 ## Vector.append v (Vector.append w (a ## vec_nil))) (shift_counter x) =
  vec_pos (a ## Vector.append v w) x.
Proof.
  rewrite /shift_counter [in RHS](eq_sym (pos_lr_both _ _ x)).
  case: (pos_both (1 + k) k' x) => [Y|Y].
  - have [->|[Y' ->]] := pos_S_inv Y.
    + by rewrite !vec_app_eq /= !vec_pos_app_right.
    + by rewrite !vec_app_eq /= !vec_pos_app_left.
  - by rewrite !vec_app_eq /= !vec_pos_app_right !vec_pos_app_left.
Qed.

Lemma vec_change_shift_counter {x a v w a' v' w' n} :
  Vector.append (a' ## v') w' = vec_change (Vector.append (a ## v) w) x n ->
  vec_change (0 ## Vector.append v (Vector.append w (a ## vec_nil))) (shift_counter x) n =
  (0 ## Vector.append v' (Vector.append w' (a' ## vec_nil))).
Proof.
  rewrite /shift_counter [in (vec_change _ x _)](eq_sym (pos_lr_both _ _ x)).
  case: (pos_both (1 + k) k' x) => [Y|Y].
  - have [->|[Y' ->]] := pos_S_inv Y.
    + rewrite !vec_app_eq !vec_app_cons /= !vec_change_app_right /= -!vec_app_eq.
      by move=> /Vector.cons_inj [<-] /vec_append_inj [<- <-].
    + rewrite !vec_app_eq !vec_app_cons /= !vec_change_app_left -!vec_app_eq.
      by move=> /Vector.cons_inj [<-] /vec_append_inj [<- <-].
  - rewrite !vec_app_eq !vec_app_cons /= !vec_change_app_right !vec_change_app_left -!vec_app_eq.
    by move=> /Vector.cons_inj [<-] /vec_append_inj [-> ->].
Qed.

Lemma simulation_mma_sss i instr a v w i' a' v' w' : 
  1 <= i < S (length P) ->
  mma_sss instr (i, a ## (Vector.append v w)) (i', a' ## (Vector.append v' w')) ->
  mma_sss (shift_instr instr) (shift_addr i, Vector.append (0 ## v) (Vector.append w (a ## vec_nil))) (shift_addr i', Vector.append (0 ## v') (Vector.append w' (a' ## vec_nil))).
Proof.
  move E1: ((i, a ## Vector.append v w)) => iavw.
  move E2: ((i', a' ## Vector.append v' w')) => i'a'v'w' Hi Hinstr.
  rewrite (shift_addr_range i). { lia. }
  case: Hinstr i a v w i' a' v' w' Hi E1 E2.
  - move=> > ? /=.
    move=> /pair_equal_spec [<- <-] /pair_equal_spec [->] E3.
    apply: in_mma_sss_inc'. { apply: shift_addr_range. lia. }
    by rewrite vec_pos_shift_counter (vec_change_shift_counter E3).
  - move=> > ? i > ?.
    move=> /pair_equal_spec [??] /pair_equal_spec [?]. subst.
    move=> /Vector.cons_inj [?] /vec_append_inj [??]. subst.
    rewrite (shift_addr_range). { lia. }
    apply: in_mma_sss_dec_0'; [done..|].
    by rewrite vec_pos_shift_counter.
  - move=> > ? i > ?.
    move=> /pair_equal_spec [??] /pair_equal_spec [?] E3. subst.
    rewrite /=.
    apply: in_mma_sss_dec_1'; [done| |rewrite vec_pos_shift_counter; eassumption].
    by rewrite (vec_change_shift_counter E3).
Qed.

Lemma simulation_sss_step i a v w i' a' v' w' : 
  sss_step (mma_sss (n:=num_counters)) (1, P) (i, a ## (Vector.append v w)) (i', a' ## (Vector.append v' w')) ->
  sss_step (mma_sss (n:=num_counters')) (1, P') (shift_addr i, Vector.append (0 ## v) (Vector.append w (a ## vec_nil))) (shift_addr i', Vector.append (0 ## v') (Vector.append w' (a' ## vec_nil))).
Proof.
  rewrite /P'. move=> [offset'] [l] [instr] [r] [v''].
  move=> [[<-]] /[dup] HP.
  move=> -> [/config_eqE2] [->] [->] [-> ->] Hinstr.
  eexists 1, (map shift_instr l), (shift_instr instr), (map shift_instr r ++ _), _.
  split; [|split].
  - congr pair. by rewrite map_app /= -app_assoc.
  - congr pair. rewrite length_map shift_addr_range //.
    rewrite HP length_app /=. lia.
  - apply: simulation_mma_sss Hinstr.
    rewrite HP length_app /=. lia.
Qed.

Lemma shift_addr_outcode i :
  i < 1 \/ S (length P) <= i ->
  shift_addr i = S (length P).
Proof.
  move: i => [|i] Hi /=; [done|].
  case E: (S (length P) - i) => [|?]; [done|].
  cbn in *. lia.
Qed.

Inductive sync : nat * Vector.t nat num_counters -> nat * Vector.t nat num_counters' -> Prop :=
  | sync_intro {i a v w} : sync
      (i, Vector.append (a ## v) w)
      (shift_addr i, Vector.append (0 ## v) (Vector.append w (a ## vec_nil))).

Lemma syncE s s' : sync s s' ->
  let avw := Vector.splitat _ (snd s) in
  let i := fst s in
  let a := Vector.hd (fst avw) in
  let v := Vector.tl (fst avw) in
  let w := snd avw in
  s = (i, Vector.append (a ## v) w) /\
  s' = (shift_addr i, Vector.append (0 ## v) (Vector.append w (a ## vec_nil))).
Proof.
  case => /= >. by rewrite Vector.splitat_append.
Qed.

Lemma vec_change_F1' n v w {m m' : nat} :
  vec_change (vec_app (n ## v) (vec_app w (m ## vec_nil))) F1' m' = vec_app (n ## v) (vec_app w (m' ## vec_nil)).
Proof.
  by rewrite !vec_change_app_right.
Qed.

Lemma finalization v w n m : 
  (1, P') //
  (S (length P), Vector.append (n ## v) (Vector.append w (m ## vec_nil))) ->>
  (5 + length P, Vector.append ((n+m) ## v) (Vector.append w (0 ## vec_nil))).
Proof.
  exists (2+m*2+1). 
  econstructor.
  { eexists 1, _, _, _, _. split; [reflexivity|split].
    - rewrite length_map. reflexivity.
    - by constructor. }
  econstructor.
  { eexists 1, (map shift_instr P ++ [INC F1']), _, _, _.
    rewrite -app_assoc. split; [reflexivity|split].
    - rewrite length_app length_map /=. congr pair. lia.
    - apply: in_mma_sss_dec_1'; [done..|].
      by rewrite !vec_app_eq !vec_pos_app_right !vec_change_app_right !vec_pos_app_right. }
  rewrite -/(Nat.add _ _).
  rewrite !vec_app_eq !vec_pos_app_right !vec_change_app_right /=.
  elim: m n.
  { move=> n. rewrite Nat.add_0_r.
    econstructor; [|econstructor].
    eexists 1, (map shift_instr P ++ [_; _; _]), _, _, _.
    rewrite -app_assoc. split; [reflexivity|split].
    - rewrite length_app length_map /=. congr pair. lia.
    - apply: in_mma_sss_dec_0'; [done..|].
      by rewrite (vec_pos_app_right (n ## v)) vec_pos_app_right. }
  move=> m IH n.
  econstructor.
  { eexists 1, (map shift_instr P ++ [_; _; _]), _, _, _.
    rewrite -app_assoc. split; [reflexivity|split].
    - rewrite length_app length_map /=. congr pair. lia.
    - apply: in_mma_sss_dec_1'; [done..|].
      by rewrite (vec_pos_app_right (n ## v)) vec_pos_app_right. }
  econstructor.
  { eexists 1, (map shift_instr P ++ [_; _]), _, _, _.
    rewrite -app_assoc. split; [reflexivity|split].
    - rewrite length_app length_map /=. congr pair. lia.
    - by apply: in_mma_sss_inc'. }
  have := IH (S n). rewrite -(Nat.add_succ_comm n m).
  congr sss_steps. congr pair.
  by rewrite vec_change_F1' -!vec_app_eq.
Qed.

#[local] Notation step1 := (sss_step (@mma_sss num_counters) (1, P)).
#[local] Notation step2 := (sss_step (@mma_sss num_counters') (1, P')).

Lemma fstep s t s' : step1 s t -> sync s s' ->
  exists t', clos_trans _ step2 s' t' /\ sync t t'.
Proof.
  move=> + /syncE /= [Hs ?]. subst s'.
  rewrite Hs.
  move: (fst s) => i.
  move: (Vector.hd (snd s)) => a.
  move: (Vector.splitat _ (Vector.tl (snd s))) => [v w] /=.
  move: t => [i' a'v'w'].
  rewrite (Vector.eta a'v'w') (vec_append_splitat (VectorDef.tl a'v'w')) Vector.splitat_append.
  move=> /simulation_sss_step ?. eexists.
  by split; [apply: t_step; eassumption|apply: sync_intro].
Qed.

Lemma step2_det s' t1' t2' :
  sss_step (@mma_sss _) (1, P') s' t1' ->
  sss_step (@mma_sss _) (1, P') s' t2' -> t1' = t2'.
Proof.
  apply: sss_step_fun. by apply: mma_sss_fun.
Qed.

Lemma simulation v v' w' c m :
  (1, P) // (1, 0 ## Vector.append v (Vector.const 0 k')) ->> (c, m ## (Vector.append v' w')) ->
  c < 1 \/ S (length P) <= c ->
  (1, P') // (1, 0 ## Vector.append v (Vector.const 0 (k' + 1))) ->>
  (5 + length P, m ## (Vector.append v' (Vector.append w' (0 ## vec_nil)))).
Proof.
  move=> /sss_compute_iff.
  move=> /(Sim.clos_refl_trans_transport fstep) => /(_ _ sync_intro).
  move=> [t'] [/syncE] /=. rewrite Vector.splitat_append /=.
  move=> [?] -> + /shift_addr_outcode Hc.
  rewrite Nat.sub_0_r Hc vec_append_const => H1.
  apply: sss_compute_trans; apply /sss_compute_iff; [eassumption|].
  by apply /sss_compute_iff /finalization.
Qed.

End FixedMMA.
End MMA_MMA_mon.
Import MMA_MMA_mon.

Theorem MMA_computable_to_MMA_mon_computable k (R : Vector.t nat k -> nat -> Prop) :
  MMA_computable R -> MMA_mon_computable R.
Proof.
  move=> /MMA_computable_iff [k'] [P] [H1P H2P].
  apply /MMA_mon_computable_iff.
  exists (k'+1), (@P' _ _ P). split; [by apply: P'_mon|split].
  - move=> v m /H1P [c] [v'] [] /=.
    rewrite (vec_append_splitat v').
    move=> /simulation /[apply] ?.
    eexists _, _. split; [eassumption|].
    rewrite /= length_P' /=. lia.
  - move=> v /(sss_terminates_iff (@mma_sss_total_ni _)) Hv. apply: H2P.
    apply /(sss_terminates_iff (@mma_sss_total_ni _)). move: Hv.
    apply /(Sim.terminates_reflection (Sim.deterministic_uniformly_confluent _ step2_det) fstep (sss_step_or_stuck (@mma_sss_total_ni _) 1 P)).
    rewrite -vec_append_const. by apply: sync_intro.
Qed.
