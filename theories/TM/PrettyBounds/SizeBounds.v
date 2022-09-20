From Undecidability Require Import MaxList.
From Undecidability Require Import TM.Util.TM_facts TM.Code.CodeTM.

From Undecidability Require Import TM.Util.VectorPrelim.

(* MOVE : this file contains general lemmas from is all over the place... *)

From Undecidability Require Import L.Prelim.MoreList.

Lemma size_list X sigX (cX: codable sigX X) (l:list X) :
  size l = sumn (map size l) + length l + 1.
Proof.
  unfold size. cbn. rewrite encode_list_concat.
  rewrite app_length, length_concat, map_map. cbn.
  change S with (fun x => 1 + x). rewrite sumn_map_add,sumn_map_c. setoid_rewrite map_length.
  cbn.  nia.
Qed.
