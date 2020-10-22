(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction(s):
    Halting of Minsky machines with two counters (MM2_HALTING) to
    Halting of one counter machines with denominators at most 4 (CM1c4_HALT)
*)

Require Import List.
Import ListNotations.
Require Import PeanoNat Lia Relations.Relation_Operators Relations.Operators_Properties.

Require Import Undecidability.MinskyMachines.MM2.
Require Undecidability.CounterMachines.CM1.
From Undecidability.CounterMachines.Util Require Import 
  Nat_facts List_facts CM1_facts MM2_facts.

Require Import ssreflect ssrbool ssrfun.

Module Argument.
Section MM2_CM1.
  Variable (P: list mm2_instr). (* MM2 program *)
  Variables (a0 b0: nat). (* MM2 initial counters *)

  (* encode start counters *)
  Definition encode_init : list CM1.Instruction :=
    (map (fun i => (1+i, 0)) (seq 0 (a0 + b0))) ++ (* a0+b0 times 2/1 *)
    (map (fun i => (1+i, 1)) (seq (a0 + b0) b0)). (* b0 times 3/2 *)

  (* instruction index map *)
  Definition fs (i: nat) : CM1.State :=
    if i is S i then i*6 + a0 + b0 + b0 else (length P)*6 + a0 + b0 + b0.

  (** encode instruction mmi at position i using index map fs for current cm1 state p *)
  Definition encode_instruction (mmi: mm2_instr) (i: nat) : list CM1.Instruction :=
    let p := fs i in
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

  (* one counter machine encoding P in start cofiguration (1, (a0, b0)) *)
  Definition M : list CM1.Instruction :=
    encode_init ++ flat_map (fun '(a, i) => encode_instruction a i) (combine P (seq 1 (length P))).

  (* M has denominators of at most 4 *)
  Lemma M_capped : CM1.capped M 4.
  Proof.
    rewrite /M /CM1.capped ?Forall_norm flat_map_concat_map Forall_concatP ?Forall_mapP ?Forall_forall.
    constructor; first by (constructor; lia).
    move=> [+ i] _. move=> [||?|?] /=; rewrite ?Forall_norm; by lia.
  Qed.

  (* κ a b c encodes mm2 counters (a, b) *)
  Definition κ (a b c: nat) : nat := 2 ^ a * 3 ^ b * 5 ^ c.

  (* encode mm2 config as cm1 config *)
  Definition encodes_config (x: mm2_config) (y: CM1.Config) : Prop :=
    match x with
    | (i, (a, b)) => CM1.state y = fs i /\ exists n, CM1.value y = κ a b n
    end.

  Lemma length_encode_instruction {mmi: mm2_instr} {i: nat} :
    length (encode_instruction mmi i) = 6.
  Proof. by move: mmi=> [||?|?]. Qed.

  Lemma length_encode_init : length encode_init = a0 + b0 + b0.
  Proof. by rewrite /encode_init app_length ?map_length ?seq_length. Qed.

  Lemma length_M : length M = length encode_init + (length P) * 6.
  Proof.
    rewrite /M app_length. f_equal.
    move: (n in seq n _). elim: P; first done.
    move=> [||?|?] P' IH /= n; by rewrite IH.
  Qed.

  Lemma seek_M n {mmi l r}: 
    P = l ++ mmi :: r -> n < 6 ->
    nth_error M (n + fs (1 + (length l))) = 
      nth_error (encode_instruction mmi (1 + length l)) n.
  Proof.
    rewrite /M. move=> + ?. move: {1 3}(1) => m. elim: l P m.
      move=> P' m -> /=. rewrite nth_error_app2 length_encode_init; first by lia.
      rewrite nth_error_app1; 
        [ by rewrite length_encode_instruction; lia | by do 2 f_equal; lia].
    move=> ? l IH P' m -> /=.
    have -> : (m + S (length l)) = (S m + length l) by lia.
    rewrite -(IH (l ++ mmi :: r) (S m)) /fs /=; first done.
    rewrite [nth_error (encode_init ++ _) _]nth_error_app2 length_encode_init; first by lia.
    rewrite [nth_error (encode_init ++ _) _]nth_error_app2 length_encode_init; first by lia.
    rewrite [nth_error (encode_instruction _ _ ++ _) _]nth_error_app2 length_encode_instruction; first by lia.
    f_equal. by lia.
  Qed.

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

  Lemma κ_21 {a b c: nat} : κ a b c * 2 / 1 = κ (1+a) b c.
  Proof.
    rewrite /κ /= Nat.div_1_r. by lia.
  Qed.

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
    rewrite [(_ * 5^_) mod 2]Nat.mul_mod; first by lia.
    rewrite [(_ * 3^_) mod 2]Nat.mul_mod; first by lia.
    rewrite pow_3_mod_2 pow_5_mod_2.
    move: a => [|a]; first done.
    have -> : 2 ^ S a = 2 * 2 ^ a by move=> /=; lia.
    by rewrite [(2 * _) mod 2]Nat.mul_mod; first by lia.
  Qed.

  Lemma κ_mod3 {a b c: nat} : 
    κ a b c mod 3 = if b is 0 then (S (locked (κ a b c) mod 3 - 1)) else 0.
  Proof.
    rewrite /κ -lock.
    rewrite [(_ * 5^_) mod 3]Nat.mul_mod; first by lia.
    rewrite [(_ * 3^_) mod 3]Nat.mul_mod; first by lia.
    move: b => [|b].
      by case: (pow_2_mod_3 a); case: (pow_5_mod_3 c); move=> -> ->.
    have -> : 3 ^ S b = 3 * 3 ^ b by move=> /=; lia.
    rewrite [(3 * _) mod 3]Nat.mul_mod; first by lia.
    by rewrite ?((@Nat.mod_same 3 ltac:(lia)), (@Nat.mod_0_l 3 ltac:(lia)), Nat.mul_0_r).
  Qed.

  Lemma κ_mod4 {a b c: nat} : κ (2+a) b c mod 4 = 0.
  Proof.
    apply /Nat.div_exact; first by lia.
    have -> : κ (2+a) b c = (κ a b c) * 4 by (rewrite /κ /=; lia).
    by rewrite /κ Nat.div_mul /=; lia.
  Qed.

  (* use: rewrite ?κ_norm. *)
  Definition κ_norm := (@κ_pos, @κ_21, @κ_32, @κ_43, @κ_54, @κ_mod2, @κ_mod3, @κ_mod4).

  Lemma κ_inj1 {a1 b1 c1 a2 b2 c2: nat} : 
    κ a1 b1 c1 = κ a2 b2 c2 -> a1 = a2.
  Proof.
    elim: a1 a2 b1 b2.
      move=> [|a2] >; first done.
      move /(f_equal (fun x => x mod 2)). by rewrite ?κ_mod2.
    move=> a1 IH [|a2] >.
      move /(f_equal (fun x => x mod 2)). by rewrite ?κ_mod2.
    move /(f_equal (fun x => x * 3 / 2)). rewrite ?κ_32. by move /IH => ->.
  Qed.

  Lemma κ_inj2 {a1 b1 c1 a2 b2 c2: nat} : 
    κ a1 b1 c1 = κ a2 b2 c2 -> b1 = b2.
  Proof.
    elim: b1 b2 a1 a2.
      move=> [|b2] >; first done.
      move /(f_equal (fun x => x mod 3)). by rewrite ?κ_mod3.
    move=> b1 IH [|b2] >.
      move /(f_equal (fun x => x mod 3)). by rewrite ?κ_mod3.
    move /(f_equal (fun x => x * 4 / 3)). rewrite ?κ_43. by move /IH => ->.
  Qed.

  Lemma fs_inj {i j: nat} : fs i = fs j -> 0 < i <= length P -> i = j.
  Proof. rewrite /fs. by move: i j => [|i] [|j]; lia. Qed.

  Lemma encodes_configP {i a b c: nat} : 
    encodes_config (i, (a, b)) {| CM1.state := fs i; CM1.value := κ a b c |}.
  Proof. constructor; by [| eexists]. Qed.

  (* M simulates each step of P *)
  Lemma P_to_M_step {x y: mm2_config} {x': CM1.Config} : 
    mm2_step P x y -> encodes_config x x' -> 
    exists n, encodes_config y (Nat.iter n (CM1.step M) x').
  Proof.
    move: x x' => [i [a b]] [p c] [mmi] /=. rewrite /mm2_instr_at. 
    move=> [[l] [r]] [HP] <-. move=> + [->] [n ->]. move Hx: (x in mm2_atom _ x) => x Hxy.
    case: Hxy Hx HP => {x}.
    (* case mm2_inc_a *)
    - move=> > [<-] <- <- HP. exists 1 => /=.
      rewrite (seek_M 0 HP ltac:(lia)) /= ?κ_norm /=.
      constructor; [done | by eexists].
    (* case mm2_inc_b *)
    - move=> > [<-] <- <- HP. exists 2 => /=.
      rewrite (seek_M 0 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 1 HP ltac:(lia)) /= ?κ_norm /=.
      constructor; [done | by eexists].
    (* mm2_dec_a j success *)
    - move=> ? j a' ? [_] -> <- HP. exists 3 => /=.
      rewrite (seek_M 0 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 4 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 5 HP ltac:(lia)) /= ?κ_norm /=.
      constructor; [done | by eexists].
    (* mm2_dec_b j success *)
    - move=> ? j ? b' [_] <- -> HP. exists 2 => /=.
      rewrite (seek_M 0 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 4 HP ltac:(lia)) /= ?κ_norm /=.
      constructor; [done | by eexists].
    (* mm2_dec_a j fail *)
    - move=> ? j ? [<-] -> <- HP. exists 4 => /=.
      rewrite (seek_M 0 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 1 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 2 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 3 HP ltac:(lia)) /= ?κ_norm /=.
      constructor; [done | by eexists].
    (* mm2_dec_b j fail *)
    - move=> ? j ? [<-] <- -> HP. exists 4 => /=.
      rewrite (seek_M 0 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 1 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 2 HP ltac:(lia)) /= ?κ_norm /=.
      rewrite (seek_M 3 HP ltac:(lia)) /= ?κ_norm /=.
      constructor; [done | by eexists].
  Qed.

  (* M simulates P *)
  Lemma P_to_M (x y: mm2_config) (x': CM1.Config) : 
    clos_refl_trans _ (mm2_step P) x y -> encodes_config x x' -> 
    exists n, encodes_config y (Nat.iter n (CM1.step M) x').
  Proof.
    move /clos_rt_rtn1_iff. elim; first by (move=> ?; exists 0).
    move=> {}y z /P_to_M_step IH _ + Hx => /(_ Hx) [m /IH] [n Hn].
    exists (m + n). by rewrite iter_plus.
  Qed.

  (* if P stops, then M stops *)
  Lemma P_stop_to_M_halting (x: mm2_config) (x': CM1.Config) :
    mm2_stop P x -> encodes_config x x' -> CM1.halting M x'.
  Proof.
    rewrite /mm2_stop /mm2_step /encodes_config.
    move: x => [i [a b]] Hi [Hsx'] [n _].
    apply /haltingP. left => /=.
    suff: not (fs i < length M) by lia.
    rewrite /fs length_M length_encode_init.
    case: i Hi {Hsx'}; first by lia.
    move=> i Hi ?.
    have /mm2_mmi_lookup [mmi Hmmi] : i < length P by lia.
    have [y ?] := (mm2_progress (mmi := mmi) (x := (S i, (a, b)))).
    apply: Hi. exists mmi. constructor; last by eassumption.
    eexists. eexists. constructor; first by eassumption.
    rewrite firstn_length_le /=; by lia.
  Qed.

  Lemma init_M_a0 (n: nat) : n <= a0 + b0 -> 
    Nat.iter n (CM1.step M) {| CM1.state := 0; CM1.value := 1 |} = 
      {| CM1.state := n; CM1.value := κ n 0 0 |}.
  Proof.
    elim: n; first done.
    move=> n IH ? /=. rewrite IH /=; first by lia.
    rewrite /M nth_error_app1; first by (rewrite length_encode_init; lia).
    rewrite /encode_init nth_error_app1; first by (rewrite map_length seq_length; lia).
    rewrite nth_error_map nth_error_seq /=; first by lia.
    by rewrite ?κ_norm.
  Qed.

  Lemma init_M_b0 (n: nat) : n <= b0 -> 
    Nat.iter n (CM1.step M) {| CM1.state := a0+b0; CM1.value := κ (a0+b0) 0 0 |} = 
      {| CM1.state := a0+b0+n; CM1.value := κ (a0+(b0-n)) n 0 |}.
  Proof.
    elim: n; first by rewrite ?nat_norm.
    move=> n IH ? /=. rewrite IH /=; first by lia.
    rewrite /M nth_error_app1; first by (rewrite length_encode_init; lia).
    rewrite /encode_init nth_error_app2; first by (rewrite map_length seq_length; lia).
    rewrite nth_error_map map_length seq_length nth_error_seq /=; first by lia.
    have -> : (a0 + (b0 - n)) = S (a0 + (b0 - n) - 1) by lia.
    rewrite ?κ_norm. by do 2 f_equal; lia.
  Qed.

  Lemma init_M_a0_b0 :
    Nat.iter (a0+b0+b0) (CM1.step M) {| CM1.state := 0; CM1.value := 1 |} = 
      {| CM1.state := a0+b0+b0; CM1.value := κ a0 b0 0 |}.
  Proof.
    rewrite iter_plus.
    rewrite init_M_a0; first by lia.
    rewrite init_M_b0; first by lia.
    do 2 f_equal. by lia.
  Qed.

  (* if M stops, then P stops *)
  Lemma M_terminating_to_P_terminates (x: mm2_config) (x': CM1.Config) {n: nat}: 
    encodes_config x x' ->
    CM1.halting M (Nat.iter n (CM1.step M) x') ->
    mm2_terminates P x.
  Proof.
    elim: n x x'.
    {
      move=> /= [i [a b]] x' [] + + /haltingP => -> [n ->] [HMi | Hκ]; first last.
        suff: if κ a b n is 0 then False else True by rewrite Hκ.
        by rewrite ?κ_norm.
      eexists. constructor; first by apply: rt_refl.
      move=> y [mmi] [/= /mm2_instr_at_bounds + _].
      move: HMi. rewrite length_M length_encode_init /fs.
      case: i; by lia.
    }
    move=> n IH x x' Hxx'.
    case: (mm2_step_or_halt P x); first last.
      move=> *. exists x. constructor; [by apply: rt_refl | done].
    move=> [y Hxy]. have [[/= Hyx' _|n']]:= P_to_M_step Hxy Hxx'.
      (* contradiction: x step y and x ~ y *)
      exfalso. apply: (mm2_step_neq Hxy).
      move: Hxy Hxx' Hyx' => [? [/mm2_instr_at_bounds + _]]. clear.
      move: x y => [xi [xa xb]] [yi [ya yb]] /= Hxi [-> [? ->]] [Hfs [? Hκ]].
      by rewrite (fs_inj Hfs Hxi) (κ_inj1 Hκ) (κ_inj2 Hκ).
    move=> Hy /(halting_monotone (m:= S n' + n)) => /(_ ltac:(lia)).
    rewrite iter_plus. move /(IH _ _ Hy) => [z] [? ?].
    exists z. constructor; last done.
    apply: rt_trans; last by eassumption. by apply: rt_step.
  Qed.

End MM2_CM1.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* halting of Minsky machines with two counters 
  many-one reduces to halting of one counter machines with denominators at most 4 *)
Theorem reduction : MM2_HALTING ⪯ CM1.CM1c4_HALT.
Proof.
  exists (fun '(P, a0, b0) => exist _ (Argument.M P a0 b0) (Argument.M_capped P a0 b0)).
  move=> [[P a0] b0]. rewrite /CM1.CM1c4_HALT /CM1.CM1_HALT /=. constructor.
  - move=> [i [/Argument.P_to_M Hi]] /Argument.P_stop_to_M_halting => /(_ a0 b0).
    case: (Hi a0 b0 {| CM1.state := a0 + b0 + b0; CM1.value := Argument.κ a0 b0 0 |});
      first by apply: Argument.encodes_configP.
    move=> n Hn /(_ _ Hn) ?.
    exists ((a0+b0+b0) + n). by rewrite iter_plus Argument.init_M_a0_b0.
  - move=> [n] /(halting_monotone (m := a0 + b0 + b0 + n)) => /(_ ltac:(lia)).
    rewrite [Nat.iter (_ + n) _ _]iter_plus Argument.init_M_a0_b0.
    apply /Argument.M_terminating_to_P_terminates.
    by apply: Argument.encodes_configP.
Qed.
