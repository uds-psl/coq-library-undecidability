(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Finite Multiset Constraint Solvability (FMsetC_SAT)
  to:
    Linear Polynomial (over N) Constraint Solvability (LPolyNC_SAT)
*)

Require Import List PeanoNat Lia Permutation.
Import ListNotations.

Require Import Undecidability.SetConstraints.FMsetC.
Require Import Undecidability.PolynomialConstraints.LPolyNC.

Require Import Undecidability.Synthetic.Definitions.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Module Argument.
Local Arguments poly_add !p !q.

Local Notation "p ≃ q" := (poly_eq p q) (at level 65).
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).

Lemma poly_add_nthP {i p q} : nth i (poly_add p q) 0 = (nth i p 0) + (nth i q 0).
Proof. elim: i p q => [|i IH] [|a p [|b q]] /=; by [|lia]. Qed.

Definition encode_msetc (c : msetc) : polyc :=
  match c with
  | msetc_zero x => polyc_one x
  | msetc_sum x y z => polyc_sum x y z
  | msetc_h x y => polyc_prod x y
  end.

(* count the number of occurrences of each element *)
Fixpoint mset_to_poly (A: list nat) := 
  match A with
  | [] => []
  | a :: A => poly_add (repeat 0 a ++ [1]) (mset_to_poly A)
  end.

Lemma mset_to_poly_shift {a A B} : mset_to_poly (A ++ a :: B) ≃ mset_to_poly (a :: A ++ B).
Proof.
  elim: A; first done.
  move=> c A + i => /(_ i) /=. rewrite ?poly_add_nthP. by lia.
Qed.

Lemma mset_to_poly_appP {A B} : mset_to_poly (A ++ B) ≃ poly_add (mset_to_poly A) (mset_to_poly B).
Proof. 
  elim: A; first done.
  move=> a A + i => /(_ i) /=. rewrite ?poly_add_nthP. by lia.
Qed.

Lemma mset_to_poly_mapP {A} : mset_to_poly (map S A) ≃ 0 :: mset_to_poly A.
Proof. 
  elim: A; first by (case; [done | by case]).
  move=> a A + i => /(_ i). case: i.
  - by rewrite /map -/(map _ _) ?poly_add_nthP.
  - move=> i. rewrite /map -/(map _ _) /mset_to_poly -/(mset_to_poly).
    rewrite /= ?poly_add_nthP /=. by lia.
Qed.

Lemma poly_add_0I {p q r} : r ≃ [] -> p ≃ q -> p ≃ poly_add q r.
Proof.
  move=> + + i => /(_ i) + /(_ i). rewrite poly_add_nthP.
  case: i=> /=; by lia.
Qed.

Lemma poly_shiftI {p} : poly_mult [0; 1] p ≃ (0 :: p).
Proof.
  rewrite /poly_mult => i /=. rewrite poly_add_nthP /=.
  have ->: nth i (map (fun=> 0) p) 0 = 0. { by elim: i p => [|i IH] [|? p] /=. }
  move: i => [|i] /=; first done.
  rewrite poly_add_nthP.
  have ->: nth i [0] 0 = 0. { by move: i => [|[|i]]. }
  elim: i p => [|i IH] [|? p] /=; by [|lia].
Qed.

Lemma mset_to_poly_eqI {A B} : A ≡ B -> mset_to_poly A ≃ mset_to_poly B.
Proof.
  move=> /Permutation_count_occ. elim: A B.
  - by move=> B /Permutation_nil ->.
  - move=> a A IH B /[dup] /(Permutation_in a) /(_ (in_eq _ _)).
    move=> /(@in_split nat) [B1 [B2 ->]] /(@Permutation_cons_app_inv nat) /IH {}IH i.
    move: (IH i) (@mset_to_poly_shift a B1 B2 i).
    rewrite /= !poly_add_nthP. by lia.
Qed.

Lemma completeness {l} : FMsetC_SAT l -> LPolyNC_SAT (map encode_msetc l).
Proof.
  move=> [φ]. rewrite -Forall_forall => Hφ.
  exists (fun x => mset_to_poly (φ x)). rewrite -Forall_forall Forall_map.
  apply: Forall_impl; last by eassumption. case.
  - by move=> x /= /mset_to_poly_eqI.
  - move=> x y z /= /mset_to_poly_eqI + i => /(_ i) ->.
    by apply mset_to_poly_appP.
  - move=> x y /= /mset_to_poly_eqI + i => /(_ i) ->.
    move: (@poly_shiftI (mset_to_poly (φ y)) i) => /= ->.
    by apply: mset_to_poly_mapP.
Qed.

Fixpoint poly_to_mset (p: list nat) := 
  match p with
  | [] => []
  | a :: p => (repeat 0 a) ++ map S (poly_to_mset p)
  end.

Lemma count_occ_poly_to_msetP {a p}: count_occ Nat.eq_dec (poly_to_mset p) a = nth a p 0.
Proof.
  elim: a p.
  - case; first done.
    move=> + p /=. elim; first by elim: (poly_to_mset p).
    by move=> ? /= ->.
  - move=> i IH. case; first done.
    move=> a p /=. rewrite count_occ_app.
    rewrite -(count_occ_map S Nat.eq_dec) ?IH; first by lia.
    by elim a.
Qed.

Lemma poly_to_mset_eqI {p q} : p ≃ q -> poly_to_mset p ≡ poly_to_mset q.
Proof. move=> + a. by rewrite ?count_occ_poly_to_msetP. Qed.

Lemma poly_to_mset_addP {p q} : poly_to_mset (poly_add p q) ≡ poly_to_mset p ++ poly_to_mset q.
Proof. move=> a. by rewrite count_occ_app ? count_occ_poly_to_msetP poly_add_nthP. Qed.

Lemma poly_to_mset_consP {p} : poly_to_mset (0 :: p) = map S (poly_to_mset p).
Proof. done. Qed.

Lemma soundness {l} : LPolyNC_SAT (map encode_msetc l) -> FMsetC_SAT l.
Proof.
  have eq_trans A B C : A ≡ B -> B ≡ C -> A ≡ C.
  { move=> H1 H2 c. by rewrite (H1 c) (H2 c). }
  move=> [ψ]. rewrite -Forall_forall Forall_map => Hψ.
  exists (fun x => poly_to_mset (ψ x)). rewrite -Forall_forall.
  apply: Forall_impl; last by eassumption. case.
  - by move=> x /= /poly_to_mset_eqI.
  - move=> x y z /= /poly_to_mset_eqI. move /eq_trans. apply.
    by apply: poly_to_mset_addP.
  - move=> x y /= /poly_to_mset_eqI. move /eq_trans. apply.
    move: (ψ y) => p. rewrite -poly_to_mset_consP. apply: poly_to_mset_eqI.
    by apply: poly_shiftI.
Qed.

End Argument.

(* many-one reduction from FMsetC_SAT to LPolyNC_SAT *)
Theorem reduction : FMsetC_SAT ⪯ LPolyNC_SAT.
Proof.
  exists (map Argument.encode_msetc) => l. constructor.
  - exact Argument.completeness.
  - exact Argument.soundness.
Qed.
