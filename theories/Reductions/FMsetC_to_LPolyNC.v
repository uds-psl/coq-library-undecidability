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

(* count the number of occurrences of each element *)
Fixpoint mset_to_poly (A: list nat) := 
  match A with
  | [] => []
  | a :: A => poly_add (repeat 0 a ++ [1]) (mset_to_poly A)
  end.

(* list facts *)
Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : 
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  elim: l.
    move=> /=. by constructor.
  move=> a l IH /=. by rewrite ? Forall_norm IH.
Qed.

Lemma map_0P {X: Type} {A: list X} : (map (fun=> 0) A) = repeat 0 (length A).
Proof. 
  elim: A.
    done.
  move=> a A IH /=. by f_equal.
Qed.

Lemma nth_consP {X: Type} {n} {a b: X} {A}: nth (S n) (a :: A) b = nth n A b.
Proof. done. Qed.

Lemma count_occ_repeat {a n} : count_occ Nat.eq_dec (repeat a n) a = n.
Proof.
  elim: n.
    done.
  move=> n /= ->. by case: (Nat.eq_dec a a).
Qed.

Lemma count_occ_S_repeat {a n} : count_occ Nat.eq_dec (repeat 0 n) (S a) = 0.
Proof.
  elim: n.
    done.
  by move=> n /= ->.
Qed.

Lemma count_occ_0_map {A} : count_occ Nat.eq_dec (map S A) 0 = 0.
Proof.
  elim: A.
    done.
  by move=> a A /= ->.
Qed.

(* poly facts *)
Lemma poly_eq_refl {p} : p ≃ p.
Proof. done. Qed. 

Lemma poly_eq_sym {p q} : p ≃ q -> q ≃ p.
Proof.
  by move=> + i => /(_ i) ->.
Qed.

Lemma poly_eq_trans {p q r} : p ≃ q -> q ≃ r -> p ≃ r.
Proof.
  by move=> + + i => /(_ i) + /(_ i) => -> ->.
Qed.

Lemma poly_add_nthP {i p q} : nth i (poly_add p q) 0 = (nth i p 0) + (nth i q 0).
Proof. 
  elim: i p q.
    case.
      done.
    move=> a p. case.
      move=> /=. by lia.
    done.
  move=> i IH. case.
    done.
  move=> a p. case.
    move=> /=. by lia.
  by move=> b q /=.
Qed.

Lemma poly_add_comm {p q} : poly_add p q = poly_add q p.
Proof.
  elim: p q.
    by case.
  move=> a p IH. case.
    done.
  move=> b q /=. f_equal.
    by lia.
  done.
Qed.

Lemma poly_add_assoc {p q r} : poly_add p (poly_add q r) ≃ poly_add (poly_add p q) r.
Proof. 
  move=> i. rewrite ? poly_add_nthP. by lia.
Qed.

Lemma repeat_0P {n} : repeat 0 n ≃ [].
Proof. 
  elim: n.
    done.
  move=> n + i => /(_ (Nat.pred i)).
  case: i.
    done.
  by case.
Qed.

Lemma poly_eq_consI {a b p q} : a = b -> p ≃ q -> a :: p ≃ b :: q.
Proof. 
  move=> -> + i => /(_ (Nat.pred i)).
  by case i.
Qed.

Lemma poly_eq_consE {a b p q} : a :: p ≃ b :: q -> a = b /\ p ≃ q.
Proof.
  move=> H. constructor.
    by move: (H 0).
  move=> i. by move: (H (S i)).
Qed.

Lemma poly_eq_nilE {a p} : a :: p ≃ [] -> a = 0 /\ p ≃ [].
Proof.
  move=> Hp. constructor.
    by move: (Hp 0).
  move=> i. move: (Hp (S i)). by case: i.
Qed.

Lemma poly_eq_nilI {a p} : a = 0 -> p ≃ [] -> a :: p ≃ [].
Proof.
  move=> -> + i => /(_ (Nat.pred i)).
  case: i.
    done.
  by case.
Qed.

Lemma mset_to_poly_shift {a A B} : mset_to_poly (A ++ a :: B) ≃ mset_to_poly (a :: A ++ B).
Proof.
  elim: A.
    done.
  move=> c A + i => /(_ i) /=.
  rewrite ? poly_add_nthP. by lia.
Qed.

Lemma mset_to_poly_appP {A B} : mset_to_poly (A ++ B) ≃ poly_add (mset_to_poly A) (mset_to_poly B).
Proof. 
  elim: A.
    done.
  move=> a A + i => /(_ i) /=. rewrite ? poly_add_nthP. by lia.
Qed.  

Lemma mset_to_poly_mapP {A} : mset_to_poly (map S A) ≃ 0 :: mset_to_poly A.
Proof. 
  elim: A.
    case.
      done.
    by case.
  move=> a A + i => /(_ i). case: i.
    rewrite /map -/(map _ _) /mset_to_poly -/(mset_to_poly).
    rewrite ? nth_consP ? poly_add_nthP.
    by move=> /=.
  move=> i. rewrite /map -/(map _ _) /mset_to_poly -/(mset_to_poly).
  rewrite ? nth_consP ? poly_add_nthP.
  move=> /=. by lia.
Qed.

Lemma poly_add_0I {p q r} : r ≃ [] -> p ≃ q -> p ≃ poly_add q r.
Proof. 
  elim: p q r.
    elim.
      move=> r /= *. by apply: poly_eq_sym.
    move=> b q IH. case.
      done.
    move=> c r /poly_eq_nilE [-> Hr] /poly_eq_sym /poly_eq_nilE [-> Hq] /=.
    apply: poly_eq_sym. apply: poly_eq_nilI.
      done.
    apply: poly_eq_sym. apply: IH.
      done.
    by apply: poly_eq_sym.
  move=> a p IH. case.
    move=> r ? /=.
    move /poly_eq_trans. apply. by apply: poly_eq_sym.
  move=> b q. case.
    done.
  move=> c r /poly_eq_nilE [->] Hr /=. rewrite Nat.add_0_r.
  move /poly_eq_consE => [<- ?].
  apply: poly_eq_consI.
    done.
  by apply: IH.
Qed.

Lemma poly_shiftI {p} : (0 :: p) ≃ poly_mult [0; 1] p.
Proof.
  rewrite /poly_mult map_0P.
  rewrite [poly_add (repeat _ _) _] poly_add_comm.
  apply: poly_add_0I.
    by apply: repeat_0P.
  under map_ext => a. have -> : 1 * a = a by lia. over.
  rewrite -/(poly_eq _ _) map_id. apply: poly_eq_consI.
    done.
  apply: poly_add_0I.
    apply: (repeat_0P (n := 1)).
  done.
Qed.

Lemma mset_to_poly_eqI {A B} : A ≡ B -> mset_to_poly A ≃ mset_to_poly B.
Proof.
  elim: A B.
    by move=> B /mset_eq_utils.eq_nilE ->.
  move=> a A IH. move=> B /mset_eq_utils.eq_consE [B1 [B2 [-> /IH {}IH]]].
  apply: poly_eq_sym.
  apply: (poly_eq_trans mset_to_poly_shift) => /=. 
  move=> i. move: (IH i).
  rewrite ? poly_add_nthP. by lia.
Qed.

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
    apply: (poly_eq_trans _ poly_shiftI).
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
    case.
      done.
    move=> a p /=.
    rewrite mset_utils.count_occ_app count_occ_repeat count_occ_0_map.
    by lia.
  move=> i IH. case.
    done.
  move=> a p /=. rewrite mset_utils.count_occ_app.
  rewrite -(count_occ_map _ Nat.eq_dec Nat.eq_dec).
    move=> ? ?. by case.
  by rewrite count_occ_S_repeat IH.
Qed.

Lemma poly_to_mset_eqI {p q} : p ≃ q -> poly_to_mset p ≡ poly_to_mset q.
Proof. 
  move=> + a. rewrite ? count_occ_poly_to_msetP. by apply.
Qed.

Lemma poly_to_mset_addP {p q} : poly_to_mset (poly_add p q) ≡ poly_to_mset p ++ poly_to_mset q.
Proof. 
  move=> a. by rewrite count_occ_app ? count_occ_poly_to_msetP poly_add_nthP.
Qed.

Lemma poly_to_mset_consP {p} : poly_to_mset (0 :: p) = map S (poly_to_mset p).
Proof. done. Qed.

Lemma soundness {l} : LPolyNC_SAT (encode_problem l) -> FMsetC_SAT l.
Proof.
  move=> [ψ]. rewrite -Forall_forall Forall_mapP => Hψ.
  exists (fun x => poly_to_mset (ψ x)). rewrite -Forall_forall.
  apply: Forall_impl; last by eassumption. case.
  - by move=> x /= /poly_to_mset_eqI.
  - move=> x y z /= /poly_to_mset_eqI. move /mset_eq_utils.eq_trans. apply.
    by apply: poly_to_mset_addP.
  - move=> x y /= /poly_to_mset_eqI. move /mset_eq_utils.eq_trans. apply.
    move: (ψ y) => p. rewrite -poly_to_mset_consP. apply: poly_to_mset_eqI.
    apply: poly_eq_sym.
    by apply: (poly_eq_trans _ poly_shiftI).
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
(* Print Assumptions FMsetC_to_LPolyNC. *)

From Undecidability Require Import Problems.TM.
From Undecidability Require Reductions.H10UC_to_FMsetC.

(* undecidability of LPolyNC *)
Theorem LPolyNC_undec : Halt ⪯ LPolyNC_SAT.
Proof.
  apply (reduces_transitive H10UC_to_FMsetC.FMsetC_undec).
  apply FMsetC_to_LPolyNC.
Qed.

Check LPolyNC_undec.
(* Print Assumptions LPolyNC_undec. *)
