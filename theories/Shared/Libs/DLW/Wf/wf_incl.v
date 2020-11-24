(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Wellfounded.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import php.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import acc_irr measure_ind wf_chains.

Set Implicit Arguments.

(* Results about the well-foundedness of strict (reverse)
    inclusion between lists 

    These proofs avoid the need of decidable equality
    and use the finitary Pigeon Hole Principle (PHP) 
    instead
*)

Section sincl.

  (* Strict inclusion between lists is a well founded relation *)

  Variable (X : Type).

  Implicit Type (l m : list X).
    
  (* sincl l m if incl l m and there is a witness in m \ l *)

  Definition sincl l m := incl l m /\ exists x, ~ In x l /\ In x m.

  (* Any n-chain m ~~> l contains a 
     duplication-free subset of l of size n 
     which does not intersect m  *)

  Lemma sincl_chain n m l :   
       chain sincl n m l -> incl m l 
                         /\ exists ll, ~ list_has_dup ll 
                                      /\ length ll = n 
                                      /\ incl ll l
                                      /\ forall x, In x m -> In x ll -> False.
  Proof.
    induction 1 as [ m | n m l k H1 H2 (H7 & ll & H3 & H4 & H5 & H6) ].
    + split.
      * intros ?; auto.
      * exists nil; simpl; repeat split; auto.
        - inversion 1.
        - intros _ [].
    + split.
      * intros ? ?; apply H7, H1; auto.
      * destruct H1 as (G1 & x & G2 & G3).
        exists (x::ll); simpl; repeat split; auto.
        - contradict H3.
          apply list_has_dup_cons_inv in H3.
          destruct H3 as [ H3 | ]; auto.
          destruct (H6 x); auto.
        - apply incl_cons; auto.
        - intros y F1 [ F2 | F2 ]; subst.
          ** tauto.
          ** apply (H6 y); auto.
  Qed.

  (* Hence, by the PHP, if there is a n-chain to l then n must be less than length l *)

  Corollary sincl_chain_bounded l m n : chain sincl n m l -> n <= length l.
  Proof.
    intros H.
    apply sincl_chain in H.
    destruct H as (_ & ll & H1 & H2 & H3 & _).
    destruct (le_lt_dec n (length l)) as [ | C ]; auto.
    subst; destruct H1.
    apply finite_php_dup with l; auto.
  Qed.

  (* Hence sincl is well-founded because n-chains to l have length bounded by length l *)
   
  Theorem wf_sincl : well_founded sincl.
  Proof.
    apply wf_chains.
    intros l; exists (length l).
    intros ? ?; apply sincl_chain_bounded.
  Qed.

End sincl.

Arguments wf_sincl {X}.

Section rincl_fin.

  (* Strict reverse inclusion between lists is well founded over a finite domain *)
 
  (* M the upper-bound/finiteness of the domain *)

  Variable (X : Type) (M : list X). 

  (* l cap M strictly contains in m cap M *)

  Definition rincl_fin l m := (forall x, In x m -> In x M -> In x l) 
                            /\ exists x, ~ In x m /\ In x l /\ In x M.

  (* Any n-chain m ~~> l contains a duplication-free subset of M of size n *)
                            
  Lemma rincl_fin_chains n m l :   chain rincl_fin n m l 
                   -> exists ll, ~ list_has_dup ll 
                                /\ incl ll M 
                                /\ length ll = n 
                                /\ incl ll m.
  Proof.
    induction 1 as [ x | n m k l H1 H2 (ll & H3 & H4 & H5 & H6) ].
    + exists nil.
      repeat split; simpl; auto; inversion 1.
    + destruct H1 as (H1 & a & G1 & G2 & G3).
      exists (a::ll).
      repeat split.
      * contradict H3.
        apply list_has_dup_cons_inv in H3.
        destruct H3 as [ H3 | ]; auto.
        destruct G1; apply H6; auto.
      * apply incl_cons; auto.
      * simpl; f_equal; auto.
      * apply incl_cons; auto.
        intros ? ?; auto.
  Qed.

  (* Hence, by the PHP, if there is a n-chain to l then n is less than length M *)

  Corollary rincl_fin_chain_bounded l m n : chain rincl_fin n m l -> n <= length M.
  Proof.
    intros H.
    apply rincl_fin_chains in H.
    destruct H as (ll & H1 & H2 & H3 & _).
    destruct (le_lt_dec n (length M)) as [ | C ]; auto.
    subst n; destruct H1.
    apply finite_php_dup with M; auto.
  Qed.

  Theorem wf_rincl_fin : well_founded rincl_fin.
  Proof.
    apply wf_chains.
    intros l; exists (length M).
    intros ? ?; apply rincl_fin_chain_bounded.
  Qed.

End rincl_fin.

Arguments wf_rincl_fin {X}.
