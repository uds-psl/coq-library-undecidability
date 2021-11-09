(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Two Counter Machine Halting (CM2_HALT)
  to:
    Halting of one counter machines with denominators at most 4 (CM1_HALT)
*)

Require Import List PeanoNat Lia.
Import ListNotations.

Require Undecidability.CounterMachines.CM2.
Require Undecidability.CounterMachines.CM1.
Import CM2 (CM2_HALT). Import CM1 (CM1_HALT).

From Undecidability.CounterMachines.Util Require Import 
  Nat_facts List_facts.

From Undecidability.CounterMachines.Util Require CM1_facts CM2_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Module Argument.
Import CM2 (Cm2).
Import CM1 (Cm1).

Section MM2_CM1.
  Variable (P: Cm2). (* CM2 program *)

  (* instruction index map *)
  Definition fs (i: nat) : CM1.State := i*6.

  (* encode instruction mmi at position i using index map fs for current cm1 state p *)
  Definition encode_instruction : CM2.Instruction * nat -> list CM1.Instruction :=
    fun '(cm2i, i) => let p := fs i in
      match cm2i with
      | CM2.inc false => 
        [(fs (1+i), 0)] ++ (* 2/1, goto i+1 *)
        [(0, 0); (0, 0); (0, 0); (0, 0); (0, 0)] (* filler *)
      | CM2.inc true => 
        [(1+p, 0); (fs (1+i), 1)] ++ (* 2/1; 3/2, goto i+1 *)
        [(0, 0); (0, 0); (0, 0); (0, 0)] (* filler *)
      | CM2.dec false j => 
        [(4+p, 1)] ++ (* 3/2 *)
        [(2+p, 0); (3+p, 0); (fs (1+i), 3)] ++ (* fail: 2/1; 2/1; 5/4 goto i+1 *)
        [(5+p, 2); (fs j, 3)] (* success: 4/3; 5/4 goto j *) 
      | CM2.dec true j => [(4+p, 2)] ++ (* 4/3 *)
        [(2+p, 0); (3+p, 0); (fs (1+i), 3)] ++ (* fail: 2/1; 2/1; 5/4 goto i+1 *)
        [(fs j, 3)] ++ (* success: 5/4 goto j *) 
        [(0, 0)] (* filler *)
      end.

  Local Arguments encode_instruction : simpl never.
  
  (* one counter machine encoding P in start cofiguration (1, (a0, b0)) *)
  Definition M : list CM1.Instruction :=
    flat_map encode_instruction (combine P (seq 0 (length P))).

  (* M has denominators of at most 4 *)
  Lemma M_capped : Forall (fun '(_, n) => n < 4) M.
  Proof.
    apply /Forall_flat_map /Forall_forall.
    move=> [[]] [] > _ /=; by (do ? constructor).
  Qed.

  (* κ a b c encodes mm2 counters (a, b) *)
  Definition κ (a b c: nat) : nat := 2 ^ a * 3 ^ b * 5 ^ c.

  (* encode mm2 config as cm1 config *)
  Definition encodes_config (x: CM2.Config) (y: CM1.Config) : Prop :=
    CM1.state y = fs (CM2.state x) /\ 
    exists n, CM1.value y = κ (CM2.value1 x) (CM2.value2 x) n.

  Local Arguments encodes_config !x !y /.

  Lemma encodes_config_init : encodes_config
    {| CM2.state := 0; CM2.value1 := 0; CM2.value2 := 0 |}
    {| CM1.state := 0; CM1.value := 1 |}.
  Proof. constructor; [done | by exists 0]. Qed.

  Lemma length_encode_instruction {cm2i: CM2.Instruction} {i: nat} :
    length (encode_instruction (cm2i, i)) = 6.
  Proof. by move: cm2i => [] []. Qed.

  Lemma length_M : length M = (length P) * 6.
  Proof.
    rewrite /M. elim: (P) (n in seq n _); first done.
    move=> ? ? IH n. 
    rewrite /= app_length (IH (S n)) length_encode_instruction. by lia. 
  Qed.

  Lemma seek_M n {i} :
    nth_error M (n + fs i) = 
    match n with
    | 0 | 1 | 2 | 3 | 4 | 5 => 
      obind (fun cm2i => nth_error (encode_instruction (cm2i, i)) n) (nth_error P i)
    | _ => nth_error M (n + fs i)
    end.
  Proof.
    rewrite /M.
    suff : n < 6 -> forall k,
      nth_error (flat_map encode_instruction (combine P (seq k (length P)))) (n + fs i) =
    obind (fun cm2i : CM2.Instruction => nth_error (encode_instruction (cm2i, k + i)) n) (nth_error P i).
    { move: n => [|[|[|[|[|[|?]]]]]]; last done.
      all: apply; by lia. }
    move=> Hn. elim: (P) i; first by move: n {Hn} => [|?] [|?] /=.
    move=> cm2i P' IH [|i] k /=.
    - by rewrite /fs ?Nat.add_0_r nth_error_app1 ?length_encode_instruction.
    - rewrite nth_error_app2 ?length_encode_instruction; first by (rewrite /fs; lia).
      have ->: n + fs (S i) - 6 = n + fs i by (rewrite /fs; lia).
      rewrite IH. move: (nth_error P' i) => [? /= |]; last done.
      by have ->: S (k + i) = k + S i by lia.
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
    { by case: (pow_2_mod_3 a); case: (pow_5_mod_3 c); move=> -> ->. }
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

  Lemma fs_inj {i j: nat} : fs i = fs j -> i = j.
  Proof. rewrite /fs. by lia. Qed.

  (* M simulates each step of P *)
  Lemma P_to_M_step {x: CM2.Config} {x': CM1.Config} : 
    encodes_config x x' -> 
    exists n, encodes_config (CM2.step P x) (Nat.iter n (CM1.step M) x').
  Proof.
    move: x x' => [i a b] [p c] /= [->] [k ->].
    move Hoi: (nth_error P i) => oi.
    move: oi Hoi => [cm2i|] /=; first last.
    { move=> Hi. exists 0. constructor; [done | by eexists ]. }
    move: cm2i => [] [] > Hi.
    (* case inc b *)
    - exists 2 => /=.
      rewrite (seek_M 0) Hi ?κ_norm /=.
      rewrite (seek_M 1) Hi ?κ_norm /=.
      constructor; [done | by eexists ].
    (* case inc a *)
    - exists 1 => /=.
      rewrite (seek_M 0) Hi ?κ_norm /=.
      constructor; [done | by eexists ].
    (* case dec b *)
    - move: b => [|b].
      + exists 4 => /=.
        rewrite (seek_M 0) Hi ?κ_norm /=.
        rewrite (seek_M 1) Hi ?κ_norm /=.
        rewrite (seek_M 2) Hi ?κ_norm /=.
        rewrite (seek_M 3) Hi ?κ_norm /=.
        constructor; [done | by eexists ].
      + exists 2 => /=.
        rewrite (seek_M 0) Hi ?κ_norm /=.
        rewrite (seek_M 4) Hi ?κ_norm /=.
        constructor; [done | by eexists ].
    (* case dec a *)
    - move: a => [|a].
      + exists 4 => /=.
        rewrite (seek_M 0) Hi ?κ_norm /=.
        rewrite (seek_M 1) Hi ?κ_norm /=.
        rewrite (seek_M 2) Hi ?κ_norm /=.
        rewrite (seek_M 3) Hi ?κ_norm /=.
        constructor; [done | by eexists ].
      + exists 3 => /=.
        rewrite (seek_M 0) Hi ?κ_norm /=.
        rewrite (seek_M 4) Hi ?κ_norm /=.
        rewrite (seek_M 5) Hi ?κ_norm /=.
        constructor; [done | by eexists ].
  Qed.

  (* M simulates P *)
  Lemma P_to_M {n} {x: CM2.Config} {x': CM1.Config} : 
    encodes_config x x' -> 
    exists m, encodes_config (Nat.iter n (CM2.step P) x) (Nat.iter m (CM1.step M) x').
  Proof.
    elim: n x x'; first by exists 0.
    move=> n IH x x' /P_to_M_step [m1] /IH [m2].
    rewrite (ltac:(lia) : S n = 1 + n) iter_plus /=.
    exists (m1 + m2). by rewrite iter_plus.
  Qed.

  (* if P stops, then M stops *)
  Lemma P_iff_M_halting (x: CM2.Config) (x': CM1.Config) :
    encodes_config x x' -> (CM2.halting P x <-> CM1.halting M x').
  Proof.
    rewrite CM1_facts.haltingP CM2_facts.haltingP.
    move: x x' => [i a b] [? ?] /= [->] [k] ->.
    rewrite /fs length_M κ_pos'. by lia.
  Qed.

  Lemma M_terminating_to_P_terminates (x: CM2.Config) (x': CM1.Config) {n: nat}: 
    encodes_config x x' ->
    CM1.halting M (Nat.iter n (CM1.step M) x') ->
    exists m, CM2.halting P (Nat.iter m (CM2.step P) x).
  Proof.
    elim /(measure_ind id) : n x x' => n IH x.
    have : CM2.halting P x \/ not (CM2.halting P x) by (rewrite CM2_facts.haltingP; lia).
    case; first by (move=> *; exists 0).
    move=> Hx x' /copy [H1xx'] /P_to_M_step [m Hm].
    have ? : m > 0.
    {
      suff: not (m = 0) by lia. move=> ?. subst m.
      apply: Hx. rewrite /CM2.halting.
      move: x' x (CM2.step P x) H1xx' Hm.
      move=> [? ?] [? ? ?] [? ? ?] /= [->] [? ->] [+] [?].
      by move=> /fs_inj -> /copy [/κ_inj1 ->] /κ_inj2 ->.
    }
    have [?|Hn] : n <= m \/ m < n by lia.
    - move: Hm => /P_iff_M_halting HPM.
      move=> /(CM1_facts.halting_monotone (m := m)) => /(_ ltac:(done)).
      move=> /HPM ?. by exists 1.
    - have ->: n = m + (n - m) by lia. rewrite iter_plus.
      move: Hm => /IH {}IH /IH => /(_ ltac:(lia)) [m' ?].
      exists (1+m'). by rewrite iter_plus.
  Qed.

End MM2_CM1.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* two counter machine halting many-one reduces to 
   halting of one counter machines with denominators at most 4 *)
Theorem reduction : CM2_HALT ⪯ CM1_HALT.
Proof.
  exists (fun P => exist _ (Argument.M P) (Argument.M_capped P)).
  move=> P. constructor.
  - move=> [n]. have := Argument.encodes_config_init.
    move=> /(Argument.P_to_M P (n := n)) [m].
    move=> /Argument.P_iff_M_halting H /H {}?.
    by exists m.
  - move=> [n]. have := Argument.encodes_config_init.
    by move=> /Argument.M_terminating_to_P_terminates H /H.
Qed.
