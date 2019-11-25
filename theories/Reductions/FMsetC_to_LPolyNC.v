(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Finite multiset constraint solvability (FMsetC)
  to:
    Linear polynomial[N] constraint solvability (LPolyNC)
*)

Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.LPolyNC Problems.FMsetC Problems.Reduction.
From Undecidability Require Import FMset.mset_utils.
From Undecidability Require FMset.mset_eq_utils.

Definition encode_msetc (c : msetc) : polyc :=
  match c with
  | msetc_zero x => polyc_one x
  | msetc_sum x y z => polyc_sum x y z
  | msetc_h x y => polyc_prod x [0; 1] y
  end.

(* encode FMsetC_PROBLEM as LPolyNC_PROBLEM *)
Definition encode_problem (msetcs : FMsetC_PROBLEM) : LPolyNC_PROBLEM :=
  map encode_msetc msetcs.

(*
(* count the number of occurrences of each element up to a bound *)
Definition mset_to_poly (A: list nat) := 
  map (fun i => count_occ (Nat.eq_dec) A i) (seq 0 (S (fold_right plus 0 A))).
*)

Fixpoint mset_to_poly (A: list nat) := 
  match A with
  | [] => []
  | a :: A => poly_add (repeat 0 a ++ [1]) (mset_to_poly A)
  end.

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : 
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
Admitted.

Lemma mset_to_poly_eqI {A B} : A ≡ B -> mset_to_poly A ≃ mset_to_poly B.
Proof. Admitted.

Lemma mset_to_poly_appP {A B} : mset_to_poly (A ++ B) ≃ poly_add (mset_to_poly A) (mset_to_poly B).
Proof. Admitted. 

Lemma mset_to_poly_mapP {A} : mset_to_poly (map S A) ≃ 0 :: mset_to_poly A.
Proof. Admitted.

Lemma poly_eq_trans {p q r} : p ≃ q -> q ≃ r -> p ≃ r.
Proof. Admitted.

Lemma map_0P {X: Type} {A: list X} : (map (fun=> 0) A) = repeat 0 (length A).
Proof. Admitted.

Lemma poly_add_0P {n p} : poly_add (repeat 0 n) p = p.
Proof. Admitted.

Lemma poly_add_comm {p q} : poly_add p q = poly_add q p.
Proof. Admitted.

Lemma completeness {l} : FMsetC_SAT l -> LPolyNC_SAT (encode_problem l).
Proof.
  move=> [φ]. rewrite -Forall_forall => Hφ.
  exists (fun x => mset_to_poly (φ x)). rewrite -Forall_forall.
  rewrite /encode_problem. rewrite Forall_mapP.
  apply: Forall_impl; last by eassumption. case.
  - move=> x /=. by move=> /mset_eq_utils.eq_symm /mset_eq_utils.eq_singletonE ->.
  - move=> x y z /= /mset_to_poly_eqI. move /poly_eq_trans. apply.
    by apply mset_to_poly_appP.
  - move=> x y /= /mset_to_poly_eqI. move /poly_eq_trans. apply.
    move: (φ y) => A. rewrite map_0P. have -> : [0] = repeat 0 1 by done.
    rewrite [poly_add _ (repeat _ _)] poly_add_comm. rewrite ? poly_add_0P.
    have -> := map_ext (fun x => x + 0) id Nat.add_0_r. rewrite map_id. 
    by apply: mset_to_poly_mapP.
Qed.
    
Fixpoint poly_to_mset (p: list nat) := 
  match p with
  | [] => []
  | a :: p => (repeat 0 a) ++ map S (poly_to_mset p)
  end.

Lemma poly_to_mset_eqI {p q} : p ≃ q -> poly_to_mset p ≡ poly_to_mset q.
Proof. Admitted.

Lemma poly_to_mset_addP {p q} : poly_to_mset (poly_add p q) ≡ poly_to_mset p ++ poly_to_mset q.
Proof. Admitted.

Lemma soundness {l} : LPolyNC_SAT (encode_problem l) -> FMsetC_SAT l.
Proof.
  move=> [ψ]. rewrite -Forall_forall Forall_mapP => Hψ.
  exists (fun x => poly_to_mset (ψ x)). rewrite -Forall_forall.
  apply: Forall_impl; last by eassumption. case.
  - by move=> x /= /poly_to_mset_eqI.
  - move=> x y z /= /poly_to_mset_eqI. move /mset_eq_utils.eq_trans. apply.
    by apply: poly_to_mset_addP.
  - move=> x y /= /poly_to_mset_eqI. move /mset_eq_utils.eq_trans. apply.
    move: (ψ y) => p. rewrite map_0P. have -> : [0] = repeat 0 1 by done.
    rewrite [poly_add _ (repeat _ _)] poly_add_comm. rewrite ? poly_add_0P.
    under map_ext => ?. rewrite Nat.add_0_r. over.
    by rewrite -/(mset_eq _ _) map_id.
Qed.

From Undecidability Require Reductions.H10UC_to_FMsetC.

(* many-one reduction from FMsetC to LPolyNC *)
Theorem FMsetC_to_LPolyNC : FMsetC_SAT ⪯ LPolyNC_SAT.
Proof.
  exists encode_problem => l. constructor.
    exact completeness.
  exact soundness.
Qed.

Check FMsetC_to_LPolyNC.
Print Assumptions FMsetC_to_LPolyNC.

From Undecidability Require Import Problems.TM.
From Undecidability Require Reductions.H10UC_to_FMsetC.

(* undecidability of LPolyNC *)
Theorem LPolyNC_undec : Halt ⪯ LPolyNC_SAT.
Proof.
  apply (reduces_transitive H10UC_to_FMsetC.FMsetC_undec).
  apply FMsetC_to_LPolyNC.
Qed.

Check LPolyNC_undec.
Print Assumptions LPolyNC_undec.
