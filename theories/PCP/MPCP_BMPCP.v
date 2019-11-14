Require Import ssreflect ssrbool ssrfun.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.PCP Problems.Reduction.

(* map a n-ary string to a binary string *)
Definition bin (x: list nat) : list bool := flat_map (fun (a : nat) => true :: (repeat false a) ++ [true])  x.

Lemma eq_binP {x y} : x = y <-> (bin x) = (bin y).
Proof.
  elim: x y.
    by case.
  move=> a x IH. case.
    done.
  move=> b y /=. constructor.
    by case=> <- <-.
  case. elim: a b.
    case=> /=.
      case. by move /IH => ->.
    done.
  move=> a IH2. case=> /=.
    done.
  move=> b. case=> /IH2. by case=> <- <-.
Qed.

Lemma bin_appP {x y} : bin (x ++ y) = bin x ++ bin y.
Proof. 
  by rewrite /bin ? flat_map_concat_map map_app concat_app.
Qed.

Definition bin_map A := map (fun '(x, y) => (bin x, bin y)) A.

Lemma map_consP {X Y: Type} {f: X -> Y} {a: X} {A : list X}: map f (a :: A) = (f a) :: map f A.
Proof. done. Qed.

Lemma tau1_bin_map {A : list (list nat * list nat)} : tau1 (bin_map A) = bin (tau1 A).
Proof.
  elim: A.
    done.
  move=> [x y] A IH.
  rewrite /bin_map map_consP /tau1 -/tau1 bin_appP. 
  by f_equal.
Qed.

Lemma tau2_bin_map {A : list (list nat * list nat)} : tau2 (bin_map A) = bin (tau2 A).
Proof.
  elim: A.
    done.
  move=> [x y] A IH.
  rewrite /bin_map map_consP /tau2 -/tau2 bin_appP. 
  by f_equal.
Qed.

Lemma Forall_consP {T: Type} {P : T -> Prop} {a: T} {l: list T} :
  Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma incl_consP {X: Type} {a: X} {A: list X} {P: list X} : (incl (a :: A) P) <-> (In a P /\ incl A P).
Proof.
  by rewrite /incl - ? Forall_forall Forall_consP. 
Qed.

(* preimage of a mapped list  *)
Lemma debin {A: list (list bool * list bool)} {P : list (list nat * list nat)} : 
  incl A (bin_map P) -> exists B, A = bin_map B /\ incl B P.
Proof.
  elim: A.
    move=> *. exists []. by constructor.
  move=> a A IH /incl_consP [+ +].
  rewrite /bin_map. move /(@in_map_iff) => [[x' y'] [? ?]]. subst a.
  move /IH => [B [? ?]]. exists ((x', y') :: B). constructor.
    by subst A.
  apply /incl_consP. by constructor.
Qed.

From Undecidability Require Import PCP.Definitions.

(* 
  many-one reduction from the modified Post correspondence problem 
  to the binary modified Post correspondence problem
*)
Theorem MPCP_to_BMPCP : MPCP ⪯ BMPCP.
Proof.
  rewrite /reduces.
  pose f := fun '((x, y), P) => ((bin x, bin y), bin_map P).
  exists f.
  move=> [[x y] P]. constructor.
    move=> [A].
    move=> [HA1 HA2].
    exists (bin_map A).
    constructor.
      move=> a.
      move /in_map_iff => [a' [?]] /HA1. subst a.
      rewrite -/(map _ ((x, y) :: P)).
      by move /(in_map (fun '(x, y) => (bin x, bin y))).
    by rewrite tau1_bin_map tau2_bin_map - ? bin_appP - eq_binP.
  move=> [A]. case.
  rewrite /bin_map -/(map _ ((x, y) :: P)) -/(bin_map _).
  move /debin => [B [? ?]]. subst A.
  rewrite tau1_bin_map tau2_bin_map - ? bin_appP.
  move /eq_binP => ?.
  exists B. by constructor.
Qed.

Check MPCP_to_BMPCP.
(* Print Assumptions MPCP_to_BMPCP. *)
