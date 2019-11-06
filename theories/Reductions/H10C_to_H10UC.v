(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Elementary Diophantine constraint solvability (H10C)
  to:
    Uniform Diophantine constraint solvability (H10UC)
*)

Require Import ssreflect ssrbool ssrfun.
Require Import List.
Import ListNotations.
Require Import PeanoNat Psatz.

From Undecidability Require Import Problems.H10C Problems.H10UC Problems.Reduction.

Set Maximal Implicit Insertion.

(* Facts about Forall, flat_map, nth *)
Section ListFacts.

Lemma Forall_cons_iff {T: Type} {P}: forall (l : list T) (a : T),
  Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  move=> *. constructor. 
    move=> H. by inversion_clear H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_app_iff {T: Type} {P}: forall (A B : list T), Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim; first by firstorder done.
  move=> ? ? IH ?.
  by rewrite - app_comm_cons ? Forall_cons_iff IH and_assoc.
Qed.

Lemma Forall_flat_map_iff {T U: Type} {P : T -> Prop} {ds : list U} {f : U -> list T} : 
  Forall P (flat_map f ds) <-> Forall (fun d => Forall P (f d)) ds.
Proof.
  elim: ds.
    constructor=> //=.
  move=> a l IH. rewrite /flat_map -/(flat_map _).
  by rewrite Forall_app_iff Forall_cons_iff IH.
Qed.

Lemma nth_default_eq {X: Type} {i d} {l: list X}: nth i l (nth i l d) = nth i l d.
Proof.
  elim: i l.
    by case.
  move=> i IH. by case.
Qed.

End ListFacts.

(* bijections between nat and nat * nat *)
Section NatNat.

(* 0 + 1 + ... + n *)
Definition big_sum (n : nat) : nat := nat_rec _ 0 (fun i m => m + (S i)) n.

(* bijection from nat * nat to nat *)
Definition nat2_to_nat '(x, y) : nat := (big_sum (x + y)) + y.

Definition next_nat2 '(x, y) : nat * nat :=
  if x is S x then (x, S y) else (S y, 0).

(* bijection from nat to nat * nat *)
Definition nat_to_nat2 (n : nat) : nat * nat :=
  Nat.iter n next_nat2 (0, 0).

Lemma nat_nat2_cancel : cancel nat2_to_nat nat_to_nat2.
Proof.
  move=> a. move Hn: (nat2_to_nat a) => n.
  elim: n a Hn.
    case; case=> [|a]; case=> [|b]=> /=; by [|lia].
  move=> n IH [x y]. case: y => [|y] /=. case: x => [|x] //=.
  all: rewrite ? (Nat.add_0_r, Nat.add_succ_r); case.
    rewrite -/(nat2_to_nat (0, x)). by move /IH ->.
  rewrite -/(nat2_to_nat (S x, y)). by move /IH ->.
Qed.

Lemma nat2_nat_cancel : cancel nat_to_nat2 nat2_to_nat.
Proof.
  elim => //=.
  move => n. move : (nat_to_nat2 n) => [+ ?].
  case => /= => [|?]; rewrite ? (Nat.add_0_r, Nat.add_succ_r) => /=; by lia.
Qed.

End NatNat.


Notation constraint x y z := (1 + x + y * y = z).
Definition sat φ l := Forall (h10uc_sem φ) l.

Lemma sat_app {φ l1 l2} : sat φ (l1 ++ l2) <-> ((sat φ l1) /\ (sat φ l2)).
  by rewrite /sat Forall_app_iff.
Qed.

Lemma sat_cons {φ c l} : sat φ (c :: l) <-> ((h10uc_sem φ c) /\ (sat φ l)).
  by rewrite /sat Forall_cons_iff.
Qed.

Lemma sat_singleton {φ c} : sat φ [c] <-> (h10uc_sem φ c).
  rewrite /sat Forall_cons_iff. constructor; by [|case].
Qed.

(* l is compatible with (f, φ) if l[i] = φ (f i) *)
Definition compatible (f φ: nat -> nat) l := forall i, nth i l (φ (f i)) = φ (f i).

Lemma compatible_cons {f φ n A}: 
  compatible f φ (n :: A) <-> (φ (f 0) = n) /\ compatible (fun i => f (1 + i)) φ A.
Proof.
  rewrite /compatible. constructor.
    move=> H. constructor.
      by move: (H 0).
    move=> i. by move: (H (1 + i)).
  move=> [? H]. by case.
Qed.

Lemma compatible_app {f φ A B}: 
  compatible f φ (A ++ B) -> compatible f φ A /\ compatible (fun i => f (length A + i)) φ B.
Proof.
  elim: A f.
    move=> /= ?. rewrite /compatible. constructor; by case.
  move=> n A IH f. rewrite - app_comm_cons. 
  move /compatible_cons=> [? ?]. constructor.
    apply /compatible_cons. constructor=> //.
    by move: (IH _ ltac:(eassumption))=> [+].
  by move: (IH _ ltac:(eassumption))=> [+].
Qed.

(* needs 2 fresh variables *)
(* x is 0 if 
  1 + x + x * x = y and
  1 + x + y * y = z and
  1 + y + x * x = z *)
Definition express_0 (x: nat) (f: nat -> nat) := [(x, x, f 0); (x, f 0, f 1); (f 0, x, f 1)].

Definition express_0f := [1; 2].

Lemma express_0E x f φ: sat φ (express_0 x f) -> φ x = 0.
Proof.
  rewrite /express_0. rewrite ? (sat_singleton, sat_cons) => /=.
  by nia.
Qed.

Lemma express_0I x f φ: φ x = 0 -> compatible f φ express_0f -> sat φ (express_0 x f).
Proof.
  rewrite /express_0. rewrite ? (sat_singleton, sat_cons). rewrite /h10uc_sem.
  move=> ? H.
  move: (H 0) (H 1) => /=.
  by nia.
Qed.

(* needs 2 fresh variables *)
(* x is 1 if 
  1 + y + y * y = x and
  1 + y + x * x = z and
  1 + x + y * y = z *)
Definition express_1 (x: nat) (f: nat -> nat) := [(f 0, f 0, x); (f 0, x, f 1); (x, f 0, f 1)].

Definition express_1f := [0; 2].

Lemma express_1E x f φ: sat φ (express_1 x f) -> φ x = 1.
Proof.
  rewrite /express_1. rewrite ? (sat_singleton, sat_cons) => /=.
  by nia.
Qed.

Lemma express_1I x f φ: φ x = 1 -> compatible f φ express_1f -> sat φ (express_1 x f).
Proof.
  rewrite /express_1. rewrite ? (sat_singleton, sat_cons). rewrite /h10uc_sem.
  move=> ? H.
  move: (H 0) (H 1) => /=.
  by nia.
Qed.

(* needs 3 fresh variables *)
(* x is 1 + y if
  1 + y + 0 * 0 = x *)
Definition express_succ (x y: nat) (f: nat -> nat) := (express_0 (f 2) f) ++ [(y, f 2, x)].

Definition express_succf := express_0f ++ [0].

Lemma express_succE x y f φ: sat φ (express_succ x y f) -> φ x = 1 + φ y.
Proof.
  rewrite /express_succ /express_0. rewrite ? (sat_singleton, sat_cons) => /=.
  by nia.
Qed.

Lemma express_succI x y f φ: φ x = 1 + φ y -> compatible f φ express_succf -> 
  sat φ (express_succ x y f).
Proof.
  rewrite /express_succ /express_succf.
  move=> ? /compatible_app [?] H.
  apply /sat_app. constructor.
    apply: express_0I=> //. by move: (H 0).
  rewrite ? (sat_singleton, sat_cons) /h10uc_sem.
  move: (H 0)=> /=.
  by nia.
Qed.

(* needs 7 fresh variables *)
(* x = y * y if 
   1 + 0 + y * y = 1 + x *)
Definition express_square (x y: nat) (f: nat -> nat) := 
  (express_0 (f 5) f) ++ (express_succ (f 6) x (fun i => f (2+i))) ++ [(f 5, y, f 6)].

Definition express_squaref φx := 
  express_0f ++ express_succf ++ [0; 1 + φx].

Lemma express_squareE x y f φ: sat φ (express_square x y f) -> φ x = (φ y) * (φ y).
Proof.
  rewrite /express_square. 
  rewrite sat_app. move=> [/express_0E ?].
  rewrite sat_app. move=> [/express_succE ?].
  rewrite ? (sat_singleton, sat_cons). rewrite /h10uc_sem.
  by nia.
Qed.

Lemma express_squareI x y f φ: φ x = φ y * φ y -> compatible f φ (express_squaref (φ x)) -> 
  sat φ (express_square x y f).
Proof.
  rewrite /express_square /express_squaref.
  move=> ? /compatible_app [?] /compatible_app [?] H.
  apply /sat_app. constructor.
    apply: express_0I=> //. by move: (H 0).
  apply /sat_app. constructor.
    apply: express_succI=> //. by move: (H 1).
  rewrite ? (sat_singleton, sat_cons). rewrite /h10uc_sem.
  move: (H 0) (H 1)=> /=.
  by nia.
Qed.

(* needs 12 fresh varaibles *)
(* x = y + y if
   1 + x + y * y = (1 + y) * (1 + y) *)
Definition express_double (x y: nat) (f: nat -> nat) := 
  (express_square (f 10) (f 11) f) ++ (express_succ (f 11) y (fun i => f (7+i))) ++ [(x, y, f 10)].

Definition express_doublef φy := 
  (express_squaref ((1 + φy) * (1 + φy))) ++ express_succf ++ 
  [(1 + φy) * (1 + φy); 1 + φy].

Lemma express_doubleE x y f φ: sat φ (express_double x y f) -> φ x = φ y + φ y.
Proof.
  rewrite /express_double. 
  rewrite sat_app. move=> [/express_squareE ?].
  rewrite sat_app. move=> [/express_succE ?].
  rewrite ? (sat_singleton, sat_cons) /h10uc_sem.
  by nia.
Qed.

Lemma express_doubleI x y f φ: φ x = φ y + φ y -> compatible f φ (express_doublef (φ y)) -> 
  sat φ (express_double x y f).
Proof.
  rewrite /express_double /express_doublef.
  move=> ? /compatible_app [?] /compatible_app [?] H.
  apply /sat_app. constructor.
    apply: express_squareI=> //. move: (H 0) (H 1)=> /=. by nia.
    move: (H 0)=> /= <-. done.
  apply /sat_app. constructor.
    apply: express_succI=> //. by move: (H 1).
  rewrite ? (sat_singleton, sat_cons) /h10uc_sem.
  move: (H 0) (H 1)=> /=.
  by nia.
Qed.

(* needs 35 fresh variables *)
(* x = x + z if
  1 + (y + y) + (1 + z) * (1 + z) = 1 + (1 + (x + x)) * z * z *)
Definition express_sum (x y z: nat) (f: nat -> nat) := 
  (express_succ (f 33) z f) ++ 
  (express_double (f 32) y (fun i => f (3+i))) ++ 
  (express_double (f 31) x (fun i => f (15+i))) ++ 
  (express_succ (f 34) (f 31) (fun i => f (27+i))) ++
  [((f 32), (f 33), (f 30)); ((f 34), z, (f 30))].

Definition express_sumf φx φy φz := 
  express_succf ++ 
  (express_doublef φy) ++ 
  (express_doublef φx) ++ 
  express_succf ++
  [1 + (φy + φy) + (1 + φz) * (1 + φz); φx + φx ; φy + φy; 1 + φz; 1 + φx + φx].

Lemma express_sumE x y z f φ: sat φ (express_sum x y z f) -> φ x = φ y + φ z.
Proof.
  rewrite /express_sum. 
  rewrite sat_app. move=> [/express_succE ?].
  rewrite sat_app. move=> [/express_doubleE ?].
  rewrite sat_app. move=> [/express_doubleE ?].
  rewrite sat_app. move=> [/express_succE ?].
  rewrite ? (sat_singleton, sat_cons) /h10uc_sem.
  by nia.
Qed.

Lemma express_sumI x y z f φ: φ x = φ y + φ z -> compatible f φ (express_sumf (φ x) (φ y) (φ z)) -> 
  sat φ (express_sum x y z f).
Proof.
  rewrite /express_sum /express_sumf.
  move=> ? /compatible_app [?] /compatible_app [?] /compatible_app [?] /compatible_app [?] H.
  apply /sat_app. constructor.
    apply: express_succI=> //. by move: (H 3)=> /=.
  apply /sat_app. constructor.
    apply: express_doubleI=> //. by move: (H 2).
  apply /sat_app. constructor.
    apply: express_doubleI=> //. by move: (H 1).
  apply /sat_app. constructor.
    apply: express_succI=> //. move: (H 1) (H 4) => /=. by lia.
  rewrite ? (sat_singleton, sat_cons) /h10uc_sem.
  move: (H 0) (H 1) (H 2) (H 3) (H 4)=> /=.
  by nia.
Qed.

(* needs 54 fresh variables *)
(* x = y * z if
  1 + (1 + (x + x) + y * y) + z * z = 1 + 1 + (y + z) * (y + z) *)
Definition express_prod (x y z: nat) (f: nat -> nat) := 
  (express_1 (f 49) f) ++ 
  (express_double (f 50) x (fun i => f (2+i))) ++
  (express_sum (f 51) y z (fun i => f (14+i))) ++ 
  [(f 50, y, f 52); (f 52, z, f 53); (f 49, f 51, f 53)].

Definition express_prodf φx φy φz := 
  express_1f ++ 
  (express_doublef φx) ++
  (express_sumf (φy + φz) φy φz) ++ 
  [1; φx + φx; φy + φz; 1 + (φx + φx) + φy * φy; 1 + 1 + (φy + φz) * (φy + φz)].

Lemma express_prodE x y z f φ: sat φ (express_prod x y z f) -> φ x = φ y * φ z.
Proof.
  rewrite /express_prod. 
  rewrite sat_app. move=> [/express_1E ?].
  rewrite sat_app. move=> [/express_doubleE ?].
  rewrite sat_app. move=> [/express_sumE ?].
  rewrite ? (sat_singleton, sat_cons) /h10uc_sem.
  by nia.
Qed.

Lemma express_prodI x y z f φ: φ x = φ y * φ z -> compatible f φ (express_prodf (φ x) (φ y) (φ z)) -> 
  sat φ (express_prod x y z f).
Proof.
  rewrite /express_prod /express_prodf.
  move=> ? /compatible_app [?] /compatible_app [?] /compatible_app [?]  H.
  apply /sat_app. constructor.
    apply: express_1I=> //. by move: (H 0).
  apply /sat_app. constructor.
    apply: express_doubleI=> //. by move: (H 1).
  apply /sat_app. constructor.
    apply: express_sumI=> //. by move: (H 2).
    by move: (H 2) => /= <-.
  rewrite ? (sat_singleton, sat_cons) /h10uc_sem.
  move: (H 0) (H 1) (H 2) (H 3) (H 4)=> /=.
  by nia.
Qed.

Definition embed '(x, y, z, i, j) : nat := nat2_to_nat (nat2_to_nat (nat2_to_nat (x, y), z), nat2_to_nat (i, j)).
Definition unembed (n: nat) : (nat * nat * nat * nat * nat) := 
  let (xyz, ij) := nat_to_nat2 n in
  let (xy, z) := nat_to_nat2 xyz in
  let (x, y) := nat_to_nat2 xy in
  let (i, j) := nat_to_nat2 ij in
  (x, y, z, i, j).

(* unembed cancels embed *)
Lemma embed_unembed {xyzij} : unembed (embed xyzij) = xyzij.
Proof.
  rewrite /embed /unembed.
  case: xyzij. case. case. case. move=> *.
  by rewrite ? nat_nat2_cancel.
Qed.

(* encode an h10 constraint as a list of uniform h10 constraints *)
Definition h10c_to_h10uc (c : h10c) : list h10uc :=
  let h x := embed (x, 0, 0, 0, 0) in
  match c with
  | h10c_one x => express_1 (h x) (fun i => embed (x, 0, 0, 1, i))
  | h10c_plus x y z => express_sum (h z) (h x) (h y) (fun i => embed (z, x, y, 2, i))
  | h10c_mult x y z => express_prod (h z) (h x) (h y) (fun i => embed (z, x, y, 3, i))
  end.

(* encoding completeness *)
Lemma h10c_sat_to_h10uc_sat_completeness (l : H10C_PROBLEM) : H10C_SAT l -> H10UC_SAT (flat_map h10c_to_h10uc l).
Proof.
  move=> [φ].
  rewrite /H10UC_SAT => H.
  pose h (x: nat) := embed (x, 0, 0, 0, 0).
  pose ψ := (fun n => 
    match unembed n with
    | (x, _, _, 0, 0) => φ x
    | (_, _, _, 1, i) => nth i express_1f 0
    | (x, y, z, 2, i) => nth i (express_sumf (φ x) (φ y) (φ z)) 0
    | (x, y, z, 3, i) => nth i (express_prodf (φ x) (φ y) (φ z)) 0
    | _ => 0
    end).

  have Hψ0 : forall x, ψ (h x) = φ x.
    move=> x. by rewrite /h /ψ embed_unembed.
  have Hψ1 : forall x y z i, (ψ (embed (x, y, z, 1, i))) = nth i express_1f 0.
    move=> *. by rewrite /ψ embed_unembed.
  have Hψ2 : forall x y z i, (ψ (embed (z, x, y, 2, i))) = nth i (express_sumf (φ z) (φ x) (φ y)) 0.
    move=> *. by rewrite /ψ embed_unembed.
  have Hψ3 : forall x y z i, (ψ (embed (z, x, y, 3, i))) = nth i (express_prodf (φ z) (φ x) (φ y)) 0.
    move=> *. by rewrite /ψ embed_unembed.
  exists ψ.

  rewrite - Forall_forall.
  elim: l H.
    by rewrite /flat_map.
  move=> c l IH H. apply /Forall_flat_map_iff. constructor; first last.
    apply /Forall_flat_map_iff. apply: IH => d ?. apply: H. by right.
  move: (H c ltac:(by left)). clear IH H. case: c.
  - move=> x. rewrite /h10c_sem /h10c_to_h10uc => Hx.
    apply: express_1I.
      by rewrite - ? /(h _) ? Hψ0.
    rewrite /compatible => i.
    rewrite - ? /(h _) ? (Hψ0, Hψ1). by rewrite nth_default_eq.
  - move=> x y z. rewrite /h10c_sem /h10c_to_h10uc => Hx.
    apply: express_sumI.
      by rewrite - ? /(h _) ? Hψ0.
    rewrite /compatible => i.
    rewrite - ? /(h _) ? (Hψ0, Hψ2). by rewrite nth_default_eq.
  - move=> x y z. rewrite /h10c_sem /h10c_to_h10uc => Hx.
    apply: express_prodI.
      by rewrite - ? /(h _) ? Hψ0.
    rewrite /compatible => i.
    rewrite - ? /(h _) ? (Hψ0, Hψ3). by rewrite nth_default_eq.
Qed.

(* encoding soundness *)
Lemma h10c_sat_to_h10uc_sat_soundness (l : H10C_PROBLEM) : H10UC_SAT (flat_map h10c_to_h10uc l) -> H10C_SAT l.
Proof.
  move=> [ψ]. rewrite - Forall_forall => Hψ.
  pose h (x: nat) := embed (x, 0, 0, 0, 0).
  pose φ x := ψ (h x).
  exists φ.
  elim: l Hψ.
    by done.
  move=> c l IH. rewrite /flat_map -/(flat_map _).  rewrite Forall_app_iff. 
  move=> [Hc H] d. rewrite /In -/(In _). case; first last.
    by apply: IH.
  move=> ?. subst d. clear IH H l.
  case: c Hc.
  all: rewrite /h10c_to_h10uc /h10c_sem.
  - move=> x. by move /express_1E.
  - move=> x y z. by move /express_sumE.
  - move=> x y z. by move /express_prodE.
Qed.
  
(* many-one reduction from H10C to H10UC *)
Theorem H10C_SAT_to_H10UC_SAT : H10C_SAT ⪯ H10UC_SAT.
Proof.
  exists (flat_map h10c_to_h10uc).
  intro l. constructor.
  - exact (@h10c_sat_to_h10uc_sat_completeness l).
  - exact (@h10c_sat_to_h10uc_sat_soundness l).
Qed.

Check H10C_SAT_to_H10UC_SAT.

From Undecidability Require Import Problems.TM.
From Undecidability Require Import Reductions.FRACTRAN_to_H10C.

(* undecidability of H10UC *)
Theorem H10UC_undec : Halt ⪯ H10UC_SAT.
Proof.
  apply (reduces_transitive H10C_undec).
  apply H10C_SAT_to_H10UC_SAT.
Qed.
  
Check H10UC_undec.
Print Assumptions H10UC_undec.
