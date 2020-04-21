
            
From Undecidability Require Import MaxList.
From Undecidability Require Import TM.TM TM.Code.CodeTM.

From Undecidability Require Import TM.VectorPrelim.

(* MOVE : this file contains general lemmas from is all over the place... *)


Lemma max_list_rec_eq_foldl (a : nat) (xs : list nat) :
  fold_left max xs a = max_list_rec a xs.
Proof.
  revert a. induction xs as [ | x xs IH]; intros; cbn in *.
  - reflexivity.
  - rewrite IH. rewrite !max_list_rec_max. nia.
Qed.

Lemma sizeOfmTapes_max_list_map (sig : Type) (n : nat) (T : tapes sig n) :
  sizeOfmTapes T = max_list_map (@sizeOfTape _) (vector_to_list T).
Proof.
  unfold sizeOfmTapes.
  rewrite fold_left_vector_to_list.
  rewrite <- vector_to_list_map.
  unfold max_list_map, max_list.
  apply max_list_rec_eq_foldl.
Qed.

Lemma sizeOfmTapes_upperBound (sig : Type) (n : nat) (tps : tapes sig n) :
  forall t, Vector.In t tps -> sizeOfTape t <= sizeOfmTapes tps.
Proof. intros. rewrite sizeOfmTapes_max_list_map. apply max_list_map_ge. now apply vector_to_list_In. Qed.

From Undecidability Require Import L.Prelim.MoreList.

Lemma max_list_sumn l : max_list l <= sumn l.
Proof.
  unfold max_list.
  induction l;cbn. 2:rewrite max_list_rec_max'. all:nia.
Qed.


Lemma right_sizeOfTape sig' (t:tape sig') :
  length (right t) <= sizeOfTape t.
Proof.
  destruct t;cbn. all:autorewrite with list;cbn. all:nia.
Qed.

Lemma length_tape_local_right sig' (t:tape sig') :
  length (tape_local (tape_move_right t)) <= sizeOfTape t.
Proof.
  destruct t;cbn.  1-3:nia. rewrite tape_local_move_right'. autorewrite with list;cbn. all:nia.
Qed.

Lemma size_list X sigX (cX: codable sigX X) (l:list X) :
  size _ l = sumn (map (size cX) l) + length l + 1.
Proof.
  unfold size. cbn. rewrite encode_list_concat.
  rewrite app_length, length_concat, map_map. cbn.
  change S with (fun x => 1 + x). rewrite sumn_map_add,sumn_map_c. setoid_rewrite map_length.
  cbn.  nia.
Qed.

Lemma destruct_vector1 (X : Type) (v : Vector.t X 1) :
  exists x, v = [| x |].
Proof. destruct_vector. eauto. Qed.
