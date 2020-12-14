Require Import List.
Import ListNotations.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Definitions.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* map a n-ary string to a binary string *)
Definition bin (x: list nat) : list bool := 
  flat_map (fun (a : nat) => true :: (repeat false a) ++ [true])  x.

Lemma eq_binP {x y} : x = y <-> (bin x) = (bin y).
Proof.
  elim: x y; first by case.
  move=> a x IH [|b y /=]; first done.
  constructor; first by move=> [<- <-].
  case. elim: a b.
  { case; last done.
    by move=> [/IH ->]. }
  move=> a IH2 [|b /=]; first done.
  by move=> [/IH2 [<- <-]].
Qed.

Lemma bin_appP {x y} : bin (x ++ y) = bin x ++ bin y.
Proof. 
  by rewrite /bin ? flat_map_concat_map map_app concat_app.
Qed.

Definition bin_map A := map (fun '(x, y) => (bin x, bin y)) A.

Lemma tau1_bin_map {A : list (list nat * list nat)} : tau1 (bin_map A) = bin (tau1 A).
Proof.
  elim: A; first done.
  move=> [x y] A IH /=. by rewrite bin_appP IH.
Qed.

Lemma tau2_bin_map {A : list (list nat * list nat)} : tau2 (bin_map A) = bin (tau2 A).
Proof.
  elim: A; first done.
  move=> [x y] A IH /=. by rewrite bin_appP IH.
Qed.

Lemma incl_consE {X: Type} {a: X} {A: list X} {P: list X} : incl (a :: A) P -> In a P /\ incl A P.
Proof.
  move=> H. constructor; move=> *; apply: H; by [left | right].
Qed.

(* preimage of a mapped list  *)
Lemma debin {A: list (list bool * list bool)} {P : list (list nat * list nat)} : 
  incl A (bin_map P) -> exists B, A = bin_map B /\ incl B P.
Proof.
  elim: A.
  { move=> *. exists []. by constructor. }
  move=> a A IH /incl_consE [+ +].
  move /(@in_map_iff) => [[x' y'] [<- ?]].
  move /IH => [B [-> HB]]. exists ((x', y') :: B). 
  constructor; first done.
  by move=> ? [<- | /HB].
Qed.

(* 
  many-one reduction from the modified Post correspondence problem 
  to the binary modified Post correspondence problem
*)
Theorem reduction : MPCP ⪯ MPCPb.
Proof.
  pose f := fun '((x, y), P) => ((bin x, bin y), bin_map P).
  exists f.
  move=> [[x y] P]. constructor; move=> [A].
  {  move=> [HA1 HA2]. exists (bin_map A).
    constructor.
    { move=> a /in_map_iff [?] [<- /HA1] ?.
      rewrite -/(map _ ((x, y) :: P)).
      by apply: in_map. }
    by rewrite tau1_bin_map tau2_bin_map -?bin_appP -eq_binP. }
  rewrite /bin_map -/(map _ ((x, y) :: P)) -/(bin_map _).
  move=> [/debin [B [-> ?]]].
  rewrite tau1_bin_map tau2_bin_map -?bin_appP -eq_binP => ?.
  by exists B.
Qed.
