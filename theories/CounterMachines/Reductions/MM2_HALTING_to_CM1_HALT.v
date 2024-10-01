(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Reduction(s):
    Halting of Minsky machines with two counters (MM2_HALTING) to
    Halting of one counter machines (CM1_HALT)
*)

Require Import ZArith List PeanoNat Lia Relations.Relation_Operators Relations.Operators_Properties.
Import ListNotations.

Require Import Undecidability.MinskyMachines.MM2.
Require Undecidability.CounterMachines.CM1.
Require Undecidability.Shared.simulation.
Require Import Undecidability.CounterMachines.Util.CM1_facts.
Require Import Undecidability.MinskyMachines.Util.MM2_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* local facts *)
Module Facts.

Lemma nth_error_seq {i start len} :
  i < len -> nth_error (seq start len) i = Some (start + i).
Proof.
  elim: len i start; first by lia.
  move=> len IH [|i] start.
  { move=> ?. congr Some. lia. }
  move=> ?. rewrite /= IH; first by lia.
  congr Some. lia.
Qed.

Lemma mul_mod (a b n : nat) :
  (a * b) mod n = (a mod n * (b mod n)) mod n.
Proof.
  move: n => [|n].
  - reflexivity.
  - apply: Nat2Z.inj. rewrite !(Nat2Z.inj_mod, Nat2Z.inj_mul).
    by apply: Z.mul_mod.
Qed.

Lemma div_exact (a b : nat) : a = b * (a / b) <-> a mod b = 0.
Proof.
  rewrite [X in X = _](Nat.div_mod_eq a b). lia.
Qed.

Lemma pow_3_mod_2 (n: nat) : 3 ^ n mod 2 = 1.
Proof.
  elim: n; first done.
  move=> n IH. by rewrite Nat.pow_succ_r' mul_mod ?IH.
Qed.

Lemma pow_5_mod_2 (n: nat) : 5 ^ n mod 2 = 1.
Proof.
  elim: n; first done.
  move=> n IH. by rewrite Nat.pow_succ_r' mul_mod ?IH.
Qed.

Lemma pow_2_mod_3 (n: nat) : 2 ^ n mod 3 = 1 \/ 2 ^ n mod 3 = 2.
Proof.
  elim: n; first by (cbn; lia).
  move=> n IH. rewrite Nat.pow_succ_r' mul_mod.
  move: IH => [->|->]; cbn; by lia.
Qed.

Lemma pow_5_mod_3 (n: nat) : 5 ^ n mod 3 = 1 \/ 5 ^ n mod 3 = 2.
Proof.
  elim: n; first by (cbn; lia).
  move=> n IH. rewrite Nat.pow_succ_r' mul_mod.
  move: IH => [->|->]; cbn; by lia.
Qed.

End Facts.

Import Facts.

Module Argument.
Import MM2Notations.

Section MM2_CM1.
  Variable (P: list mm2_instr). (* MM2 program *)
  Variables (a0 b0: nat). (* MM2 initial counters *)

  (* instruction index map *)
  Definition fs (i: nat) : nat :=
    if i is S i then i*6 + a0 + b0 + b0 else (length P * 6) + a0 + b0 + b0.

  (* encode instruction mmi at position i using index map fs for current mm2 program index p *)
  Definition encode_instruction : mm2_instr * nat -> list CM1.Instruction :=
    fun '(mmi, i) => let p := fs i in
      match mmi with
      | mm2_inc_a =>
        [(fs (1+i), 0)] ++ (* 2/1, goto i+1 *)
        [(0, 0); (0, 0); (0, 0); (0, 0); (0, 0)] (* filler *)
      | mm2_inc_b =>
        [(1+p, 0); (fs (1+i), 1)] ++ (* 2/1; 3/2, goto i+1 *)
        [(0, 0); (0, 0); (0, 0); (0, 0)] (* filler *)
      | mm2_dec_a j =>
        [(4+p, 1)] ++ (* 3/2 *)
        [(2+p, 0); (3+p, 0); (fs (1+i), 3)] ++ (* fail: 2/1; 2/1; 5/4 goto i+1 *)
        [(5+p, 2); (fs j, 3)] (* success: 4/3; 5/4 goto j *) 
      | mm2_dec_b j => [(4+p, 2)] ++ (* 4/3 *)
        [(2+p, 0); (3+p, 0); (fs (1+i), 3)] ++ (* fail: 2/1; 2/1; 5/4 goto i+1 *)
        [(fs j, 3)] ++ (* success: 5/4 goto j *) 
        [(0, 0)] (* filler *)
      end.

  Arguments encode_instruction : simpl never.

  (* one counter machine encoding P in start cofiguration (1, (a0, b0)) *)
  Definition M : list CM1.Instruction :=
    map (fun i => (1+i, 0)) (seq 0 (a0+b0)) ++
    map (fun i => (1+i, 1)) (seq (a0+b0) (b0)) ++
    flat_map encode_instruction (combine P (seq 1 (length P))).

  (* M has denominators of at most 4 *)
  Lemma M_capped : Forall (fun '(_, n) => n < 4) M.
  Proof.
    apply /Forall_app. constructor; [|apply /Forall_app; constructor]; apply /Forall_forall.
    - move=> [[]] > /in_map_iff [?] [[? <-]] _; by do ? constructor.
    - move=> [[]] > /in_map_iff [?] [[? <-]] _; by do ? constructor.
    - move=> [[]].
      + move=> [|[|[|[|?]]]]; [lia..|].
        move=> /in_flat_map [[[]?]] > [_] /=; intuition congruence.
      + move=> n [|[|[|[|?]]]]; [lia..|].
        move=> /in_flat_map [[[]?]] > [_] /=; intuition congruence.
  Qed.

  Lemma length_encode_instruction instr i : length (encode_instruction (instr, i)) = 6.
  Proof. by case: instr. Qed.

  Lemma M_length : length M = a0+b0+b0+(length P * 6).
  Proof.
    rewrite /M !length_app !length_map !length_seq.
    suff: forall n, length (flat_map encode_instruction (combine P (seq n (length P)))) = length P * 6.
    { move=> ->. lia. }
    elim: (P). { done. }
    move=> > IH > /=. by rewrite length_app length_encode_instruction IH.
  Qed.

  (* κ a b c encodes mm2 counters (a, b) *)
  Definition κ (a b c: nat) : nat := 2 ^ a * 3 ^ b * 5 ^ c.

  Arguments nth_error : simpl never.
  Arguments Nat.div : simpl never.
  Arguments Nat.modulo : simpl never.

  Lemma κ_pos {X: Type} {x y: X} {a b c: nat} : 
    match κ a b c with | 0 => x | S _ => y end = y.
  Proof.
    rewrite /κ.
    have ? := Nat.pow_nonzero 2 a ltac:(lia).
    have ? := Nat.pow_nonzero 3 b ltac:(lia).
    have ? := Nat.pow_nonzero 5 c ltac:(lia).
    by have -> : let n := 2 ^ a * 3 ^ b * 5 ^ c in n = S (n - 1) by nia.
  Qed.

  Lemma κ_pos' {a b c: nat} : κ a b c = 1 + (κ a b c - 1).
  Proof.
    have := @κ_pos _ false true a b c.
    case: (κ a b c); [done | by lia].
  Qed.

  Lemma κ_21 {a b c: nat} : κ a b c * 2 / 1 = κ (1+a) b c.
  Proof. rewrite /κ /= Nat.div_1_r. by lia. Qed.

  Lemma κ_32 {a b c: nat} : κ (1+a) b c * 3 / 2 = κ a (1+b) c.
  Proof.
    have -> : κ (1+a) b c * 3 = (3 * κ a b c) * 2 by (rewrite /κ /=; lia).
    by rewrite /κ Nat.div_mul /=; lia.
  Qed.

  Lemma κ_43 {a b c: nat} : κ a (1+b) c * 4 / 3 = κ (2+a) b c.
  Proof.
    have -> : κ a (1+b) c * 4 = (4 * κ a b c) * 3 by (rewrite /κ /=; lia).
    by rewrite /κ Nat.div_mul /=; lia.
  Qed.

  Lemma κ_54 {a b c: nat} : κ (2+a) b c * 5 / 4 = κ a b (1+c).
  Proof.
    have -> : κ (2+a) b c * 5 = (5 * κ a b c) * 4 by (rewrite /κ /=; lia).
    by rewrite /κ Nat.div_mul /=; lia.
  Qed.

  Lemma κ_mod2 {a b c: nat} : κ a b c mod 2 = if a is 0 then 1 else 0.
  Proof.
    rewrite /κ.
    rewrite [(_ * 5^_) mod 2]mul_mod.
    rewrite [(_ * 3^_) mod 2]mul_mod.
    rewrite pow_3_mod_2 pow_5_mod_2.
    move: a => [|a]; first done.
    have -> : 2 ^ S a = 2 * 2 ^ a by move=> /=; lia.
    by rewrite [(2 * _) mod 2]mul_mod.
  Qed.

  Lemma κ_mod3 {a b c: nat} : 
    κ a b c mod 3 = if b is 0 then (S (locked (κ a b c) mod 3 - 1)) else 0.
  Proof.
    rewrite /κ -lock.
    rewrite [(_ * 5^_) mod 3]mul_mod.
    rewrite [(_ * 3^_) mod 3]mul_mod.
    move: b => [|b].
    { by case: (pow_2_mod_3 a); case: (pow_5_mod_3 c); move=> -> ->. }
    have -> : 3 ^ S b = 3 * 3 ^ b by move=> /=; lia.
    replace (((3 * 3 ^ b) mod 3)) with 0.
    - by rewrite Nat.mul_0_r.
    - by rewrite mul_mod.
  Qed.

  Lemma κ_mod4 {a b c: nat} : κ (2+a) b c mod 4 = 0.
  Proof.
    apply /div_exact.
    have -> : κ (2+a) b c = (κ a b c) * 4 by (rewrite /κ /=; lia).
    by rewrite /κ Nat.div_mul /=; lia.
  Qed.

  (* use: rewrite ?κ_norm. *)
  Definition κ_norm := (@κ_pos, @κ_21, @κ_32, @κ_43, @κ_54, @κ_mod2, @κ_mod3, @κ_mod4).

  Lemma κ_inj1 {a1 b1 c1 a2 b2 c2: nat} : 
    κ a1 b1 c1 = κ a2 b2 c2 -> a1 = a2.
  Proof.
    elim: a1 a2 b1 b2.
    { move=> [|a2] >; first done.
      move /(f_equal (fun x => x mod 2)). by rewrite ?κ_mod2. }
    move=> a1 IH [|a2] >.
    { move /(f_equal (fun x => x mod 2)). by rewrite ?κ_mod2. }
    move /(f_equal (fun x => x * 3 / 2)). rewrite ?κ_32. by move /IH => ->.
  Qed.

  Lemma κ_inj2 {a1 b1 c1 a2 b2 c2: nat} : 
    κ a1 b1 c1 = κ a2 b2 c2 -> b1 = b2.
  Proof.
    elim: b1 b2 a1 a2.
    { move=> [|b2] >; first done.
      move /(f_equal (fun x => x mod 3)). by rewrite ?κ_mod3. }
    move=> b1 IH [|b2] >.
    { move /(f_equal (fun x => x mod 3)). by rewrite ?κ_mod3. }
    move /(f_equal (fun x => x * 4 / 3)). rewrite ?κ_43. by move /IH => ->.
  Qed.

  (* encode mm2 config as cm1 config *)
  Definition encodes_config (x: mm2_state) (y: CM1.Config) : Prop :=
    let: (i, (a, b)) := x in
    CM1.state y = fs i /\ 
    exists c, CM1.value y = κ a b c.

  Local Arguments encodes_config !x !y /.

  Lemma seek_M n {i mm2i} :
    mm2_instr_at mm2i i P ->
    nth_error M (n + fs i) =
    match n with
    | 0 | 1 | 2 | 3 | 4 | 5 => nth_error (encode_instruction (mm2i, i)) n
    | _ => nth_error M (n + fs i)
    end.
  Proof.
    have [->|Hn] : n = 6 + (n - 6) \/ n < 6 by lia.
    { done. }
    move=> [Pl] [Pr] [HP Hi].
    suff: nth_error M (n + fs i) = nth_error (encode_instruction (mm2i, i)) n.
    { move=> ->. by move: n Hn => [|[|[|[|[|[|?]]]]]]. }
    rewrite /M HP -Hi.
    rewrite nth_error_app2. { rewrite !length_map !length_seq /=. lia. }
    rewrite nth_error_app2. { rewrite !length_map !length_seq /=. lia. }
    rewrite !length_map !length_seq.
    suff: forall k, nth_error
      (flat_map encode_instruction (combine P (seq k (length P)))) (n + length Pl * 6) =
      nth_error (encode_instruction (mm2i, k + length Pl)) n.
    { move=> <-. rewrite HP /=. congr nth_error. lia. }
    rewrite HP. elim: Pl {HP Hi}.
    { move=> ?. rewrite /= !Nat.add_0_r.
      by rewrite nth_error_app1; [case: mm2i|]. }
    move=> instr Pl IH k.
    have ->: k + length (instr :: Pl) = (k+1) + length Pl.
    { by rewrite -Nat.add_assoc. }
    rewrite -IH /= nth_error_app2 length_encode_instruction. { lia. }
    have ->: k+1 = S k by lia.
    congr nth_error. lia.
  Qed.

  Lemma mm2_step_neq_encodes x y x' y' :
    mm2_step P x y -> encodes_config x x' -> encodes_config y y' -> x' <> y'.
  Proof.
    move=> +++?. subst y'.
    move: x' => [p c] [[]] > [/mm2_instr_at_pos + H]; case H => > /=.
    all: try match goal with |- nat -> _ => move=> ? > end.
    all: move=> -> [->] [? ->] /= [?] [?].
    all: move=> /[dup] /κ_inj1 ? /κ_inj2 ?.
    all: lia.
  Qed.

  (* M simulates each step of P *)
  Lemma P_to_M_step (x y: mm2_state) (x': CM1.Config) :
    mm2_step P x y ->
    encodes_config x x' ->
    exists y' : CM1.Config,
      clos_trans CM1.Config (fun x y => CM1.step M x = y /\ x <> y) x' y' /\
      encodes_config y y'.
  Proof.
    move=> Hxy Hxx'.
    suff: exists n, encodes_config y (Nat.iter (n+1) (CM1.step M) x').
    { move=> [n Hyy']. exists (Nat.iter (n+1) (CM1.step M) x').
      split; [|done].
      have : x' <> (Nat.iter (n+1) (CM1.step M) x').
      { move: Hxy => /mm2_step_neq_encodes. by apply. }
      elim: n x' {Hxx' Hyy'}. { move=> ? ?. by apply: t_step. }
      move=> n IH x' /=.
      have [<-|/IH] := Config_eq_dec x' (Nat.iter (n + 1) (CM1.step M) x').
      { move=> ?. by apply: t_step. }
      have [<-|] := Config_eq_dec (Nat.iter (n + 1) (CM1.step M) x') (CM1.step M (Nat.iter (n + 1) (CM1.step M) x')).
      { done. }
      move=> ???. apply: t_trans; [eassumption|].
      by apply: t_step. }
    move: Hxy Hxx' => [?] [+ Hxy].
    move: x' Hxy=> [p c] [] /= > Hinstr [-> [n ->]].
    - (* case inc a *)
      exists 0 => /=.
      rewrite (seek_M 0 Hinstr) ?κ_norm.
      constructor; [done|by eexists].
    - (* case inc b *)
      exists 1 => /=.
      rewrite (seek_M 0 Hinstr) ?κ_norm /=.
      rewrite (seek_M 1 Hinstr) ?κ_norm /=.
      constructor; [done|by eexists].
    - (* case dec a > 0 *)
      exists 2 => /=.
      rewrite (seek_M 0 Hinstr) ?κ_norm /=.
      rewrite (seek_M 4 Hinstr) ?κ_norm /=.
      rewrite (seek_M 5 Hinstr) ?κ_norm /=.
      constructor; [done|by eexists].
    - (* case dec b > 0 *)
      exists 1 => /=.
      rewrite (seek_M 0 Hinstr) ?κ_norm /=.
      rewrite (seek_M 4 Hinstr) ?κ_norm /=.
      constructor; [done|by eexists].
    - (* case dec a = 0 *)
      exists 3 => /=.
      rewrite (seek_M 0 Hinstr) ?κ_norm /=.
      rewrite (seek_M 1 Hinstr) ?κ_norm /=.
      rewrite (seek_M 2 Hinstr) ?κ_norm /=.
      rewrite (seek_M 3 Hinstr) ?κ_norm /=.
      constructor; [done |by eexists].
    - (* case dec b = 0 *)
      exists 3 => /=.
      rewrite (seek_M 0 Hinstr) ?κ_norm /=.
      rewrite (seek_M 1 Hinstr) ?κ_norm /=.
      rewrite (seek_M 2 Hinstr) ?κ_norm /=.
      rewrite (seek_M 3 Hinstr) ?κ_norm /=.
      constructor; [done|by eexists].
  Qed.

  Lemma MM2_HALTING_iff_terminates {a b} :
    MM2_HALTING (P, a, b) <->
      simulation.terminates (mm2_step P) (1, (a, b)).
  Proof. done. Qed.

  Notation cm1_step := (fun x y => CM1.step M x = y /\ x <> y).

  Lemma cm1_steps n x : clos_refl_trans _ cm1_step x (Nat.iter n (CM1.step M) x).
  Proof.
    elim: n. { apply: rt_refl. }
    move=> n IH /=.
    have [<-|?] := Config_eq_dec (Nat.iter n (CM1.step M) x) (CM1.step M (Nat.iter n (CM1.step M) x)).
    { done. }
    apply: rt_trans.
    - by apply: IH.
    - by apply: rt_step.
  Qed.

  Lemma cm1_halting_stuck x : CM1.halting M x -> simulation.stuck cm1_step x.
  Proof.
    rewrite /CM1.halting. move=> Hx y [Hxy H'xy]. congruence.
  Qed. 

  Lemma CM1_halting_iff_terminates {x} :
    (exists n, CM1.halting M (Nat.iter n (CM1.step M) x)) <->
    simulation.terminates cm1_step x.
  Proof.
    split.
    - move=> [n].
      have /(@simulation.terminates_extend CM1.Config) := cm1_steps n x.
      move: (Nat.iter n (CM1.step M) x) => y H Hy. apply: H.
      exists y. by split; [apply: rt_refl|apply: cm1_halting_stuck].
    - move=> [y] [].
      move=> /(@clos_rt_rt1n CM1.Config). elim.
      + move=> {}x /(_ (CM1.step M x)) Hx. exists 0.
        rewrite /CM1.halting /=.
        have [|] := Config_eq_dec x (CM1.step M x); [done|].
        tauto.
      + move=> > [Hxy ?] _ IH /IH [n {}IH].
        exists (n+1). by rewrite /Nat.iter nat_rect_plus /= Hxy.
  Qed.

  Lemma init_M_a0 (n: nat) : n <= a0+b0 ->
    Nat.iter n (CM1.step M) {| CM1.state := 0; CM1.value := 1 |} =
      {| CM1.state := n; CM1.value := κ n 0 0 |}.
  Proof.
    elim: n. { done. }
    move=> n /= + ? => ->. { lia. }
    rewrite /M /= κ_pos.
    rewrite nth_error_app1. { by rewrite length_map length_seq. }
    rewrite nth_error_map nth_error_seq /=. { done. }
    by rewrite κ_norm.
  Qed.

  Lemma init_M_b0 (n: nat) : n <= b0 ->
    Nat.iter n (CM1.step M) {| CM1.state := a0 + b0; CM1.value := κ (a0+b0) 0 0 |} =
      {| CM1.state := a0 + b0 + n; CM1.value := κ (a0 + b0 - n) n 0 |}.
  Proof.
    elim: n. { by rewrite Nat.sub_0_r Nat.add_0_r. }
    move=> n /= + ? => ->. { lia. }
    rewrite /M /= κ_pos.
    rewrite nth_error_app2 length_map length_seq. { lia. }
    rewrite nth_error_app1. { rewrite length_map length_seq. lia. }
    rewrite nth_error_map nth_error_seq /=. { lia. }
    rewrite κ_norm.
    have ->: a0 + b0 - n = S (a0 + b0 - n - 1) by lia.
    rewrite κ_norm.
    congr CM1.mkConfig; [|congr κ]; lia.
  Qed.

  Lemma init_M :
    Nat.iter (a0 + b0 + b0) (CM1.step M)
    {| CM1.state := 0; CM1.value := 1 |} =
      {| CM1.state := a0 + b0 + b0; CM1.value := κ a0 b0 0 |}.
  Proof.
    rewrite /Nat.iter Nat.add_comm nat_rect_plus -!/(Nat.iter _ _ _) init_M_a0. { done. }
    rewrite init_M_b0. { done. }
    rewrite (Nat.add_comm b0). congr CM1.mkConfig. congr κ. lia.
  Qed.

  Lemma transport : MM2_HALTING (P, a0, b0) -> CM1.CM1_HALT (exist _ M M_capped).
  Proof.
    move=> /MM2_HALTING_iff_terminates H.
    rewrite /CM1.CM1_HALT.
    apply /(terminating_reaches_iff init_M).
    apply /CM1_halting_iff_terminates.
    move: H. apply: simulation.terminates_transport.
    - exact: P_to_M_step.
    - rewrite /simulation.stuck.
      move=> x x' Hx Hxx'.
      rewrite /simulation.terminates.
      exists x'. split; [by apply: rt_refl|].
      rewrite /simulation.stuck.
      move=> y' [Hx'y' H'x'y'].
      move: Hx => /mm2_stop_index_iff.
      subst y'.
      move: x' Hxx' H'x'y'.
      move=> [p [|c]] /=; [done|].
      case Hinstr: (nth_error M p) => [instr|]; [|done].
      have /nth_error_Some : nth_error M p <> None by congruence.
      rewrite M_length.
      move: x => [i [a b]] /= HpM [? _] _.
      move=> [?|?]; subst.
      + move: HpM => /=. lia.
      + move: HpM. have -> /= : i = S (i-1) by lia.
        lia.
    - by split; [|exists 0].
  Qed.

  Lemma reflection : CM1.CM1_HALT (exist _ M M_capped) -> MM2_HALTING (P, a0, b0).
  Proof.
    move=> /(terminating_reaches_iff init_M) /CM1_halting_iff_terminates H.
    apply /MM2_HALTING_iff_terminates.
    move: H. apply: simulation.terminates_reflection.
    - move=> > [<- _] [<- _]. by left.
    - exact: P_to_M_step.
    - by apply: mm2_exists_step_dec.
    - by split; [|exists 0].
  Qed.

End MM2_CM1.
End Argument.

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.CounterMachines.CM1.

(* halting of Minsky machines with two counters 
  many-one reduces to halting of one counter machines *)
Theorem reduction : MM2_HALTING ⪯ CM1_HALT.
Proof.
  exists (fun '(P, a0, b0) => exist _ _ (Argument.M_capped P a0 b0)).
  intros [[P a0] b0]. constructor.
  - apply Argument.transport.
  - apply Argument.reflection.
Qed.
