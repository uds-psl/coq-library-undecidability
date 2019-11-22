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
    Finite elementary multiset constraint solvability (FMsetEC)
*)

Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.FMsetC Problems.Reduction.

From Undecidability Require Import FMset.mset_utils FMset.mset_eq_utils FMset.mset_term_utils.
Import NatNat.

Lemma nat_to_nat2_non_increasing {n} : fst (nat_to_nat2 n) + snd (nat_to_nat2 n) < S n.
Proof.
  elim: n=> [|n] //=.
  move: (nat_to_nat2 n) => [x y].
  case: y => [|y]; case: x => [|x] /=; by lia.
Qed.

Inductive tree : Set :=
  | leaf : tree
  | node : nat -> tree -> tree -> tree.

Fixpoint tree_to_nat (t: tree) : nat :=
  match t with
  | leaf => 0
  | node n t u => S (nat2_to_nat (n, nat2_to_nat ((tree_to_nat t), (tree_to_nat u))))
  end.

Lemma aux1 {n} : (fst (nat_to_nat2 (snd (nat_to_nat2 n)))) < S n.
Proof. 
  have ? := @nat_to_nat2_non_increasing n.
  have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
  by lia.
Qed.

Lemma aux2 {n} : (snd (nat_to_nat2 (snd (nat_to_nat2 n)))) < S n.
Proof. 
  have ? := @nat_to_nat2_non_increasing n.
  have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
  by lia.
Qed.
  
Definition nat_to_tree : nat -> tree.
Proof.
  apply: (Fix lt_wf _). case.
    exact (fun _ => leaf).
  move=> n f.
  pose m := snd (nat_to_nat2 n).
  refine (node (fst (nat_to_nat2 n)) (f (fst (nat_to_nat2 m)) _) (f (snd (nat_to_nat2 m)) _)).
    exact aux1.
  exact aux2.
Defined.

Lemma nat_to_tree_S_nP {n} : 
  nat_to_tree (S n) = 
    node (fst (nat_to_nat2 n)) 
      (nat_to_tree (fst (nat_to_nat2 (snd (nat_to_nat2 n)))))
      (nat_to_tree (snd (nat_to_nat2 (snd (nat_to_nat2 n))))).
Proof.
  rewrite /nat_to_tree Fix_eq=> //. elim=> // *. by f_equal.
Qed.
    
Lemma nat_tree_cancel {t} : nat_to_tree (tree_to_nat t) = t.
Proof.
  elim: t=> // *.
  rewrite /tree_to_nat nat_to_tree_S_nP nat_nat2_cancel.
  rewrite -/tree_to_nat /fst /snd -/(fst _) -/(snd _) nat_nat2_cancel. 
  by f_equal.
Qed.
    
Lemma tree_nat_cancel {n} : tree_to_nat (nat_to_tree n) = n.
Proof.
  elim /lt_wf_ind: n. case=> //.
  move=> n IH. rewrite nat_to_tree_S_nP /tree_to_nat -/tree_to_nat ? IH.
    1,2: have ? := @nat_to_nat2_non_increasing n.
    1,2: have ? := @nat_to_nat2_non_increasing (snd (nat_to_nat2 n)).
    1,2: by lia.
  rewrite - surjective_pairing nat2_nat_cancel.
  by rewrite - surjective_pairing nat2_nat_cancel.
Qed.


Fixpoint term_to_tree (t: mset_term) : tree :=
  match t with
  | mset_term_zero => node 0 leaf leaf
  | mset_term_var x => node 1 (node x leaf leaf) leaf
  | mset_term_plus t u => node 2 (term_to_tree t) (term_to_tree u)
  | mset_term_h t => node 3 (term_to_tree t) leaf
  end.

Fixpoint tree_to_term (t: tree) : mset_term :=
  match t with
  | node 0 leaf leaf => mset_term_zero
  | node 1 (node x leaf leaf) leaf => mset_term_var x
  | node 2 t u => mset_term_plus (tree_to_term t) (tree_to_term u)
  | node 3 t leaf => mset_term_h (tree_to_term t)
  | _ => mset_term_zero
  end.

Definition term_to_nat (t: mset_term) : nat :=
  tree_to_nat (term_to_tree t).

Definition nat_to_term (n: nat) : mset_term :=
  tree_to_term (nat_to_tree n).

Lemma nat_term_cancel {t} : nat_to_term (term_to_nat t) = t.
Proof.
  rewrite /nat_to_term /term_to_nat nat_tree_cancel. elim: t.
  - done.
  - done.
  - by move=> t + u /= => -> ->.
  - by move=> t /= => ->.
Qed. 

(* decompose mset_term into elementary constraints *)
Fixpoint term_to_msetcs (t: mset_term) : list msetc :=
  match t with
  | mset_term_zero => [msetc_zero (term_to_nat t)]
  | mset_term_var x => []
  | mset_term_plus u v => 
      [msetc_sum (term_to_nat t) (term_to_nat u) (term_to_nat v)] ++ 
      (term_to_msetcs u) ++ (term_to_msetcs v)
  | mset_term_h u => 
      [msetc_h (term_to_nat t) (term_to_nat u)] ++ (term_to_msetcs u)
  end.


Definition encode_eq (t u: mset_term) :=
  [(msetc_sum (tree_to_nat leaf) (tree_to_nat leaf) (tree_to_nat leaf)); 
  (msetc_sum (term_to_nat t) (tree_to_nat leaf) (term_to_nat u))].

(* encode FMsetC_PROBLEM as LPolyNC_PROBLEM *)
Definition encode_problem (msetcs : FMsetC_PROBLEM) : FMsetEC_PROBLEM :=
  flat_map (fun '(t, u) => (encode_eq t u) ++ term_to_msetcs t ++ term_to_msetcs u) msetcs.

(*
Section ForallNorm.

Variable T : Type.
Variable P : T -> Prop.

Lemma Forall_nilP : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_consP {a A} : Forall P (a :: A) <-> P a /\ Forall P A.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_singletonP {a} : Forall P [a] <-> P a.
Proof. rewrite Forall_consP Forall_nilP. by tauto. Qed.

Lemma Forall_appP {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim: A.
    constructor; by [|case].
  move=> ? ? IH /=. rewrite ? Forall_consP ? IH.
  by tauto.
Qed.

(* usage rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).

End ForallNorm.
*)

Lemma Forall_flat_mapP {X Y: Type} {P: Y -> Prop} {f: X -> list Y} {A: list X}: 
  Forall P (flat_map f A) <-> Forall (fun a => Forall P (f a)) A.
Proof.
  elim: A.
    move=> /=. by constructor.
  move=> a A IH. by rewrite /flat_map -/(flat_map _ _) ? Forall_norm IH.
Qed.

Lemma term_to_nat_pos {t} : term_to_nat t = S (Nat.pred (term_to_nat t)).
Proof.
  case: t; by move=> *. 
Qed.

Lemma completeness {l} : FMsetC_SAT l -> FMsetEC_SAT (encode_problem l).
Proof.
  move=> [φ]. rewrite -mset_satP => Hφ.
  pose ψ x := if x is 0 then [] else mset_sem φ (nat_to_term x).
  have Hψ (A) : Forall (msetc_sem ψ) (term_to_msetcs A).
  {
    elim: A.
    - by rewrite /term_to_msetcs ? Forall_norm /ψ.
    - by rewrite /term_to_msetcs.
    - move=> A IHA B IHB. 
      rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
      constructor; first last.
        by constructor.
      rewrite /ψ /msetc_sem ? nat_term_cancel.
      by rewrite ? term_to_nat_pos.
    - move=> A IH. 
      rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
      constructor; last done.
      rewrite /ψ /msetc_sem ? nat_term_cancel.
      by rewrite ? term_to_nat_pos.
  }
  exists ψ.
  rewrite - Forall_forall /encode_problem Forall_flat_mapP.
  apply: Forall_impl; last eassumption. 
  move=> [A B]. rewrite ? Forall_norm.
  move=> HφAB. constructor; first last.
    by constructor.
  constructor.
    done.
  rewrite /ψ /msetc_sem.
  rewrite (@term_to_nat_pos A) (@term_to_nat_pos B) /(tree_to_nat leaf).
  by rewrite - ? term_to_nat_pos ? nat_term_cancel.
Qed.

Print Assumptions completeness.


Lemma eq_app_nil_nilP {A} : A ≡ A ++ A -> A = [].
Proof. Admitted.

Lemma eq_mapI {A B} : A ≡ B -> map S A ≡ map S B.
Proof.
  rewrite /mset_eq => + c. move=> /(_ (Nat.pred c)).
  case: c.
    admit.
  move=> c. rewrite - ? (count_occ_map S Nat.eq_dec Nat.eq_dec); first last.
    done.
  all: move=> >; by case.
Admitted.

Lemma soundness {l} : FMsetEC_SAT (encode_problem l) -> FMsetC_SAT l.
Proof.
  move=> [ψ]. rewrite -Forall_forall Forall_flat_mapP => Hψ.
  pose φ x := ψ (term_to_nat (mset_term_var x)).
  exists φ. rewrite -mset_satP.
  apply: Forall_impl; last by eassumption.
  move=> [t u]. rewrite ? Forall_norm => [[+ [+]]].
  rewrite /msetc_sem -/(msetc_sem _). move=> [/eq_app_nil_nilP /copy [Hψ0 ->]].
  rewrite /app => Hψtu.

  have Hφ (s) : Forall (msetc_sem ψ) (term_to_msetcs s) -> mset_sem φ s ≡ (ψ (term_to_nat s)).
  {
    clear. elim: s.
    - rewrite /term_to_msetcs ? Forall_norm /msetc_sem /φ /mset_sem.
      by apply /eq_symm.
    - by move=> x _.
    - move=> t IHt u IHu.
      rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
      move=> [+ [/IHt {}IHt /IHu {}IHu]].
      rewrite /msetc_sem /φ /mset_sem -/mset_sem -/φ.
      move /eq_symm. apply /eq_trans.
      by apply: eq_appI.
    - move=> t IH.
      rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
      move=> [+ /IH {}IH].
      rewrite /msetc_sem /φ /mset_sem -/mset_sem -/φ.
      move /eq_symm. apply /eq_trans.
      by apply: eq_mapI.
  }
  move=> /Hφ Ht /Hφ Hu.
  under eq_lr; by eassumption.
Qed.
  



(*
(* inject mset_term into poly variables *)
Fixpoint term_to_nat (t: mset_term) : nat :=
  match t with
  | mset_term_zero => nat2_to_nat (0, 0)
  | mset_term_var x => nat2_to_nat (1, x)
  | mset_term_plus t u => nat2_to_nat (2, nat2_to_nat ((term_to_nat t), (term_to_nat u)))
  | mset_term_h t => nat2_to_nat (3, term_to_nat t)
  end.

Fixpoint nat_to_term

(* decompose mset_term into poly constraints *)
Fixpoint term_to_polycs (t: mset_term) : list polyc :=
  match t with
  | mset_term_zero => [polyc_sum (term_to_nat t) (term_to_nat t) (term_to_nat t)]
  | mset_term_var x => []
  | mset_term_plus u v => [polyc_sum (term_to_nat t) (term_to_nat u) (term_to_nat v)]
  | mset_term_h u => [polyc_prod (term_to_nat t) [0; 1] (term_to_nat u)]
  end.

Definition mset_eq_to_polycs (t u: mset_term) :=
  [polyc_sum (term_to_nat t) (term_to_nat mset_term_zero) (term_to_nat u); 
  (polyc_sum (term_to_nat mset_term_zero) (term_to_nat mset_term_zero) (term_to_nat mset_term_zero))].

(* encode FMsetC_PROBLEM as LPolyNC_PROBLEM *)
Definition encode_problem (msetcs : FMsetC_PROBLEM) : LPolyNC_PROBLEM :=
  flat_map (fun '(t, u) => mset_eq_to_polycs t u ++ term_to_polycs t ++ term_to_polycs u) msetcs.

Definition mset_sat (φ : nat -> list nat) (l : FMsetC_PROBLEM) := 
  Forall (fun '(A, B) => (mset_sem φ A) ≡ (mset_sem φ B)) l.

Lemma mset_satP {φ l} : mset_sat φ l <-> (forall (A B : mset_term), In (A, B) l -> (mset_sem φ A) ≡ (mset_sem φ B)).
Proof.
  rewrite /mset_sat Forall_forall. constructor.
  - move=> H A B. apply /H.
  - move=> H [A B]. apply /H.
Qed.

Lemma completeness {l} : FMsetC_SAT l -> LPolyNC_SAT (encode_problem l).
Proof.
  move=> [φ]. rewrite -mset_satP.
  rewrite /FMsetC_SAT.
*)


(* list facts *)

Lemma singleton_length {X : Type} {A : list X} : length A = 1 -> exists a, A = [a].
Proof.
  case: A.
    done.
  move => a A /=. case. move /length_zero_iff_nil => ->. by eexists.
Qed.

Lemma nil_or_ex_max (A : list nat) : A = [] \/ exists a, In a A /\ Forall (fun b => a >= b) A.
Proof.
  elim: A.
    by left.
  move=> a A. case.
    move=> ->. right. exists a. split; by [left | constructor].
  move=> [b [Hb1 Hb2]]. right.
  case: (le_lt_dec a b)=> ?.
  - exists b. split; by [right | constructor].
  - exists a. split.
      by left.
    constructor.
      done.
    move: Hb2. apply /Forall_impl => ?. by lia.
Qed.

(* count_occ facts *)
Lemma count_occ_app {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A B c}:
count_occ D (A ++ B) c = count_occ D A c + count_occ D B c.
Proof.
  elim: A B.
    done.
  move=> a A IH B /=. rewrite IH. by case: (D a c).
Qed.

Lemma count_occ_cons {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A a c}:
count_occ D (a :: A) c = count_occ D (locked [a]) c + count_occ D A c.
Proof.
  rewrite /count_occ /is_left -lock. by case: (D a c).
Qed.

(* In facts *)
Lemma in_cons_iff : forall {A : Type} {a b : A} {l : list A}, In b (a :: l) <-> (a = b \/ In b l).
Proof. by constructor. Qed.

(* Forall facts *)
Lemma Forall_nil_iff {X: Type} {P: X -> Prop} : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_cons_iff {T: Type} {P: T -> Prop} {a l} :
  Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_singleton_iff {X: Type} {P: X -> Prop} {x} : Forall P [x] <-> P x.
Proof.
  rewrite Forall_cons_iff. by constructor; [case |].
Qed.

Lemma Forall_app_iff {T: Type} {P: T -> Prop} {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim: A.
    constructor; by [|case].
  move=> ? ? IH /=. rewrite ? Forall_cons_iff ? IH.
  by tauto.
Qed.

(* usage: rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_app_iff, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).

(* Forall2 facts *)
Lemma Forall2_nil_rE {X Y: Type} {P: X -> Y -> Prop} {A}: Forall2 P A [] -> A = [].
Proof. move=> H. by inversion H. Qed.

Lemma Forall2_nil_lE {X Y: Type} {P: X -> Y -> Prop} {A}: Forall2 P [] A -> A = [].
Proof. move=> H. by inversion H. Qed.

Lemma Forall2_lastP {X Y: Type} {P: X -> Y -> Prop} {A B a b}:
  Forall2 P (A ++ [a]) (B ++ [b]) <-> Forall2 P A B /\ P a b.
Proof. 
  elim: A B => /=.
    move=> B. constructor.
      elim: B => /=.
        move=> H. by inversion H.
      move=> c B IH H. inversion H. subst.
      have := Forall2_nil_lE ltac:(eassumption). by move /app_eq_nil => [_].
    move=> [/Forall2_nil_lE ->] ? /=. by constructor.
  move=> c A IH. elim=> /=.
    constructor.
      move=> H. inversion H. subst.
      have := Forall2_nil_rE ltac:(eassumption). by move /app_eq_nil => [_].
    by move=> [/Forall2_nil_rE].
  move=> d B IH2. constructor.
    move=> H. inversion H. subst. constructor.
      constructor.
        done.
      have := iffLR (IH B) ltac:(eassumption). by case.
    have := iffLR (IH B) ltac:(eassumption). by case.
  move=> [H ?]. inversion H. subst. constructor.
    done.
  apply /IH. by constructor.
Qed.

(* seq facts *)
Lemma seq_last start length : seq start (S length) = (seq start length) ++ [start + length].
Proof.
  have -> : S length = length + 1 by lia.
  by rewrite seq_app.
Qed.

(* repeat facts *)
Lemma repeat_add {X : Type} {x : X} {m n} : repeat x (m + n) = repeat x m ++ repeat x n.
Proof.
  elim: m.
    done.
  move=> m IH. cbn. by f_equal.
Qed.

Lemma Forall_repeat {X: Type} {a} {A: list X} : Forall (fun b => a = b) A -> A = repeat a (length A).
Proof.
  elim: A.
    done.
  move=> b A IH. rewrite Forall_norm => [[? /IH ->]]. subst b.
  cbn. by rewrite repeat_length.
Qed.



(* encode a single H10UC constraint as a list of FMsetC constraints *)
Definition encode_h10uc '(x, y, z) := encode_constraint x y z.

(* many-one reduction from H10UC to FMsetC *)
Theorem H10UC_to_FMsetC : H10UC_SAT ⪯ FMsetC_SAT.
Proof.
  exists (fun h10ucs => flat_map encode_h10uc h10ucs).
  move=> h10ucs. constructor.
  - move=> [φ Hφ]. 
    exists (construct_valuation φ).
    elim: h10ucs Hφ.
      done.
    move=> [[x y] z] h10cs IH.
    move /Forall_forall. rewrite Forall_cons_iff. move=> [Hxyz /Forall_forall /IH].
    move=> {}IH A B.
    rewrite /flat_map -/(flat_map _) in_app_iff. case; first last.
      by apply /IH.
    rewrite /encode_h10uc.
    have := @encode_constraint_sat φ x y z ltac:(done).
    rewrite /mset_sat Forall_forall. by apply.
  - move=> [φ]. rewrite - mset_satP /mset_sat. move=> Hφ.
    pose ψ := (fun x => length (φ (embed (x, 0, 1)))).
    exists ψ.
    rewrite - Forall_forall.
    elim: h10ucs Hφ.
      done.
    move=> [[x y] z] h10ucs IH. rewrite /flat_map -/(flat_map _) Forall_app_iff.
    rewrite /(encode_h10uc _).
    move=> [/encode_constraint_spec Hxyz /IH ?].
    by constructor.
Qed.

Check H10UC_to_FMsetC.
(* Print Assumptions H10UC_to_FMsetC. *)

From Undecidability Require Import Problems.TM.
From Undecidability Require Import Reductions.H10C_to_H10UC.

(* undecidability of FMsetC *)
Theorem FMsetC_undec : Halt ⪯ FMsetC_SAT.
Proof.
  apply (reduces_transitive H10UC_undec).
  apply H10UC_to_FMsetC.
Qed.

Check FMsetC_undec.
(* Print Assumptions FMsetC_undec. *)
