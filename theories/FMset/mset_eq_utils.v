(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

Require Import ssreflect ssrbool ssrfun.
Require Import PeanoNat Psatz.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.FMsetC.
From Undecidability Require Import FMset.mset_utils.

Arguments mset_eq !A !B.

(* eq facts *)
Lemma eq_refl {A} : A ≡ A.
Proof. done. Qed.

Lemma eq_eq {A B}: A = B -> A ≡ B.
Proof. by move=> ->. Qed.
  
Lemma eq_symm {A B} : A ≡ B -> B ≡ A.
Proof. by firstorder done. Qed.
  
Lemma eq_in_iff {A B} : A ≡ B -> forall c, In c A <-> In c B.
Proof.
  rewrite /mset_eq => H c. constructor=> Hc.
  - have := iffLR (count_occ_In Nat.eq_dec A c) Hc.
    move: (H c) => ->.
    by move /(count_occ_In Nat.eq_dec B c).
  - have := iffLR (count_occ_In Nat.eq_dec B c) Hc.
    move: (H c) => <-.
    by move /(count_occ_In Nat.eq_dec A c).
Qed.

Lemma eq_nilE {A} : [] ≡ A -> A = [].
Proof.
  case: A.
    done.
  move=> a A /eq_in_iff /(_ a) /iffRL. apply: unnest.
    by left.
  done.
Qed.

Lemma eq_trans {A B C} : A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  rewrite /mset_eq => + + c.
  move=> /(_ c) + /(_ c).
  by move=> -> ->.
Qed.

Lemma eq_Forall_iff {A B} : A ≡ B -> forall P, (Forall P A <-> Forall P B).
Proof.
  move /eq_in_iff => H P.
  rewrite ? Forall_forall. constructor; by firstorder done.
Qed.

Lemma eq_lr {A B A' B'}:
  A ≡ A' -> B ≡ B' -> (A ≡ B) <-> (A' ≡ B').
Proof.
  move=> HA HB. constructor.
  - move /eq_trans. move /(_ _ HB). 
    move /(eq_trans _). by move /(_ _ (eq_symm HA)). 
  - move /eq_trans. move /(_ _ (eq_symm HB)). 
    move /(eq_trans _). by move /(_ _ HA).
Qed. 

Lemma eq_appI {A B A' B'} : A ≡ A' -> B ≡ B' -> A ++ B ≡ A' ++ B'.
Proof.
  rewrite /mset_eq => + + c. move=> /(_ c) + /(_ c).
  rewrite ? count_occ_app. by move=> -> ->.
Qed.

(* solves trivial multiset equalities *)
Ltac eq_trivial := 
  move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil); unlock; by lia.
    
Lemma eq_cons_iff {a A B} : (a :: A) ≡ (a :: B) <-> A ≡ B.
Proof.
  rewrite /mset_eq. constructor.
  all: move=> H c; move: {H}(H c); rewrite ? count_occ_cons ? in_cons_iff; unlock.
  all: by rewrite Nat.add_cancel_l.
Qed.

Lemma eq_app_iff {A B C} : (A ++ B) ≡ (A ++ C) <-> B ≡ C.
Proof.
  elim: A.
    done.
  move=> a A IH /=.
  by rewrite eq_cons_iff.
Qed.

Lemma eq_length {A B} : A ≡ B -> length A = length B.
  elim /(measure_ind (@length nat)) : A B.
  case.
    by move=> _ B /eq_nilE ->.
  move=> a A IH B /copy [/eq_in_iff /(_ a) /iffLR]. apply: unnest.
    by left.
  move /(@in_split _ _) => [B1 [B2 ->]].
  under (eq_lr eq_refl (B' := a :: (B1 ++ B2))).
    by eq_trivial.
  move /eq_cons_iff. move /IH. apply: unnest.
    done.
  rewrite ? app_length => /=. by lia.
Qed.

Lemma eq_repeatE {a A n} : repeat a n ≡ A -> A = repeat a n.
Proof.
  move=> /copy [/eq_length]. rewrite repeat_length => HlA.
  move /eq_Forall_iff /(_ (fun c => a = c)) /iffLR. apply: unnest.
    clear. elim: n.
      by constructor.
    firstorder (by constructor).
  subst n.
  elim: A.
    done.
  move=> b A IH /Forall_cons_iff [<-] /IH -> /=.
  by rewrite repeat_length.
Qed.

Lemma eq_singletonE {a A} : [a] ≡ A -> A = [a].
Proof.
  have -> : [a] = repeat a 1 by done.
  by move /eq_repeatE.
Qed.

Lemma eq_mapE {A} : map S A ≡ A -> A = [].
Proof.
  case (nil_or_ex_max A).
    done.
  move=> [a [Ha /Forall_forall HA]] /eq_in_iff /(_ (S a)) /iffLR.
  rewrite in_map_iff. apply: unnest.
    by exists a.
  move /HA. by lia.
Qed.

Lemma eq_consP {a A B}: a :: A ≡ a :: B <-> A ≡ B.
Proof.
  rewrite /mset_eq. constructor; move=> + c => /(_ c).
  all: rewrite ? count_occ_cons; by lia.
Qed.

Lemma eq_consE {a A B}: a :: A ≡ B -> exists B1 B2, B = B1 ++ (a :: B2) /\ A ≡ (B1 ++ B2).
Proof.
  move=> /copy [/mset_eq_utils.eq_in_iff /(_ a) /iffLR /(_ ltac:(by left))].
  move /(@in_split _ _) => [B1 [B2 ->]].
  under (mset_eq_utils.eq_lr mset_eq_utils.eq_refl (B' := a :: (B1 ++ B2))).
    by mset_eq_utils.eq_trivial.
  move /mset_eq_utils.eq_consP => H.
  exists B1, B2. by constructor.
Qed.

Lemma eq_app_nil_nilP {A B} : A ≡ A ++ B -> B = [].
Proof.
  elim: A.
    by move /eq_nilE.
  move=> a A IH /=.
  by move /eq_consP.
Qed.

Lemma eq_mapI {A B} : A ≡ B -> map S A ≡ map S B.
Proof.
  rewrite /mset_eq => + c. move=> /(_ (Nat.pred c)).
  case: c.
    move=> _. 
    have H := iffLR (count_occ_not_In _ _ _).
    rewrite ? {}H; first last.
      done.
    1-2: by rewrite in_map_iff=> [[? [? ?]]].
  move=> c. rewrite - ? (count_occ_map S Nat.eq_dec Nat.eq_dec); first last.
    done.
  all: move=> >; by case.
Qed.
