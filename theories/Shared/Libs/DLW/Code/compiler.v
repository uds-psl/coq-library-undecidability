(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils subcode.

Import ListNotations.

Set Implicit Arguments.

(* * A certified low-level compiler *)

Tactic Notation "dest" "eq" "nat" "dec" "as" simple_intropattern(H) :=
    match goal with 
      |- context[eq_nat_dec ?x ?y] => destruct (eq_nat_dec x y) as H
    end; auto.

Tactic Notation "solve" "eq" "nat" "dec" := 
    match goal with 
      |- context[eq_nat_dec ?x ?x] => destruct (eq_nat_dec x x) as [ | [] ]; [ | reflexivity ]
    end; auto.
    
Section linker.
 
  Variable (X Y : Type)
           (c : (nat -> nat) -> nat -> X -> list Y) (* instruction compiler w.r.t. a given linker & a position *)
           (lc : X -> nat)                          (* compiled code length does not depend on linker or position *)
           (Hc : forall f n x, length (c f n x) = lc x).

  Fixpoint length_compiler lx :=
    match lx with
      | nil   => 0
      | x::lx => lc x+length_compiler lx
    end.
    
  Fact length_compiler_app ll mm : length_compiler (ll++mm) = length_compiler ll + length_compiler mm.
  Proof.
    induction ll as [ | x ll IH ]; simpl; auto.
    rewrite IH; lia.
  Qed.
    
  Notation lsum := length_compiler.

  Fixpoint link i ll j : list (nat*nat) :=
    match ll with
      | nil   => nil
      | x::ll => (i,j)::link (S i) ll (lc x+j)
    end.
    
  Fact link_app i ll mm j : link i (ll++mm) j = link i ll j ++ link (length ll+i) mm (lsum ll+j).
  Proof.
    revert i j; induction ll as [ | x ll IH ]; simpl; intros i j; f_equal.
    rewrite IH; do 2 f_equal; lia.
  Qed.
  
  Fact link_fst i ll j : map fst (link i ll j) = list_an i (length ll).
  Proof.
    revert i j; induction ll; simpl; intros; f_equal; auto.
  Qed.

  Fact link_le i ll j: 
          (forall x, In x ll -> 1 <= lc x)
       -> forall p k, In (p,k) (link i ll j) -> j <= k < lsum ll + j.
  Proof.
    revert i j; induction ll as [ | x ll IH ]; simpl; intros i j Hlc p k.
    + intros [].
    + intros [ E | H ].
      * inversion E; subst p k.
        generalize (Hlc x (or_introl eq_refl)); lia.
      * apply IH in H; try lia.
        intros; apply Hlc; auto.
  Qed.

  Section comp.
  
    Variable lnk : nat -> nat.

    Fixpoint comp i ll j :=
      match ll with
        | nil   => nil
        | x::ll => c lnk i x ++ comp (S i) ll (lc x+j)
      end.
    
    Fact comp_app i ll mm j : comp i (ll++mm) j = comp i ll j ++ comp (length ll+i) mm (lsum ll+j).
    Proof.
      revert i j; induction ll as [ | x ll IH ]; simpl; intros i j; auto.
      rewrite IH; solve list eq; do 3 f_equal; lia.
    Qed.
    
    Fact comp_length i ll j : length (comp i ll j) = lsum ll.
    Proof using Hc.
      revert i j; induction ll as [ | x ll IH ]; simpl; intros i j; auto.
      rew length; rewrite IH, Hc; trivial.
    Qed.

    Fact comp_in_inv i ll j l' y r' : 
               comp i ll j = l'++y::r' 
            -> exists l x r a b, ll = l++x::r
                              /\ c lnk (length l+i) x = a++y::b
                              /\ l' = comp i l j ++ a
                              /\ r' = b ++ comp (1+length l+i) r (lsum (l++[x])+j).
    Proof.
      revert i j l' y r'; induction ll as [ | x ll IH ]; simpl; intros i j l' y r' H.
      + now destruct l'.
      + apply list_app_cons_eq_inv in H
          as [ (m & H1 & H2) | (m & H1 & H2) ].
        * apply IH in H2 as (l & x' & r & a & b & H2 & H3 & H4 & H5).
          exists (x::l), x', r, a, b; msplit 3; simpl.
          - f_equal; auto.
          - rewrite <- H3; f_equal; lia.
          - rewrite <- H1, app_ass; f_equal; auto.
          - rewrite H5; f_equal; f_equal; lia.
        * exists [], x, ll, l', m; msplit 3; auto.
          rewrite H2; do 2 f_equal; simpl; lia.
    Qed.

  End comp.

  Variable (P : nat * list X) (i : nat) (err : nat).

  Definition linker :=
    let ll := (length (snd P) + fst P,lsum (snd P)+i)::link (fst P) (snd P) i
    in fun j => match list_assoc eq_nat_dec j ll with
        | None   => err
        | Some p => p
    end.
    
  (* These two lemmas specify the linker *)
    
  Fact linker_app ll mm : snd P = ll++mm -> linker (length ll+fst P) = lsum ll + i.
  Proof.
    intros H; unfold linker.
    destruct P as (iP,lP).
    rewrite H; simpl in H |- *.
    destruct mm as [ | x mm ].
    * rewrite <- app_nil_end.
      solve eq nat dec.
    * rew length.
      dest eq nat dec as [ H1 | H1 ]; [ lia | clear H1 ].
      rewrite link_app, list_assoc_app.
      generalize (list_assoc_In eq_nat_dec (length ll + iP) (link iP ll i)).
      destruct (list_assoc eq_nat_dec (length ll + iP) (link iP ll i)) as [ j | ].
      - intros H1.
        apply in_map with (f := @fst _ _) in H1.
        rewrite link_fst, list_an_spec in H1; simpl in H1; lia.
      - intros; simpl; solve eq nat dec.
  Qed.
  
  Fact linker_err_code j : j < fst P \/ length (snd P) + fst P < j -> linker j = err.
  Proof.
    unfold linker.
    destruct P as (iP,lP); simpl; intros H.
    dest eq nat dec as [ H1 | _ ]; [ lia | ].
    generalize (list_assoc_In eq_nat_dec j (link iP lP i)).
    destruct (list_assoc eq_nat_dec j (link iP lP i)); auto.
    intros H1.
    apply in_map with (f := @fst _ _) in H1.
    rewrite link_fst, list_an_spec in H1; simpl in H1; lia.
  Qed.

  Fact linker_mono j k : fst P <= j -> j <= k -> k < length (snd P) + fst P -> linker j <= linker k.
  Proof.
    intros H1 H2 H3.
    destruct (@list_split_length _ (snd P) (j - fst P))
      as (l1 & ll & H4 & H5); try lia.
    destruct (@list_split_length _ ll (k-j))
      as (l2 & l3 & H6 & H7).
    + rewrite H4, app_length in H3; lia.
    + subst ll.
      generalize (linker_app _ _ H4); intros E1.
      rewrite <- app_ass in H4.
      generalize (linker_app _ _ H4); intros E2.
      replace (length l1+fst P) with j in E1; try lia.
      replace (length (l1++l2)+fst P) with k in E2.
      * rewrite E1, E2, length_compiler_app; lia.
      * rewrite app_length; lia.
  Qed.

  Definition compiler := comp linker (fst P) (snd P) i.
  
  Fact compiler_length : length compiler = length_compiler (snd P).
  Proof using Hc. apply comp_length. Qed.

  Section linker_in_code.

    Hypothesis (Hlc : forall x, 1 <= lc x).

    Fact linker_in_code j : in_code j P -> in_code (linker j) (i,compiler).
    Proof using Hc Hlc.
      intros H; red in H; simpl in H.
      destruct (@list_split_length _ (snd P) (j - fst P)) as (ll & mm & H1 & H2);
        try lia.
      replace j with (length ll+fst P) by lia.
      rewrite (linker_app _ _ H1).
      red; simpl; rewrite compiler_length, H1, length_compiler_app.
      rewrite H1, app_length in H.
      destruct mm as [ | x mm ]. 
      + simpl in H; lia.
      + simpl.
        generalize (Hlc x); lia.
    Qed.

  End linker_in_code.
  
  Fact compiler_subcode j x : 
          (j,x::nil) <sc P 
       -> (linker j, c linker j x) <sc (i,compiler)
       /\  linker (1+j) = lc x + linker j.
  Proof using Hc.
    case_eq P; intros iP lP HP (l & r & H1 & H2); simpl in H1.
    assert (linker j = lsum l + i) as Hj.
    { generalize (linker_app l (x::r)).
      rewrite HP; simpl; intros E.
      rewrite <- E; auto; f_equal; lia. }
    assert (linker (1+j) = lc x + linker j) as HSj.
    {  generalize (linker_app (l++x::nil) r).
      rewrite HP, app_ass; simpl; intros H3.
      specialize (H3 H1).
      eq goal H3; f_equal.
      f_equal.
      rew length; lia.
      rewrite length_compiler_app; simpl; lia. }
    split; auto.
    unfold compiler; rewrite HP, H1; simpl.
    exists (comp linker iP l i), (comp linker (1+length l+iP) r (lc x+lsum l+i)); split.
    rewrite comp_app; simpl; do 3 f_equal; lia.
    rewrite comp_length; lia.
  Qed.

  Fact compiler_subcode_inv k µ : 
            (k,[µ]) <sc (i,compiler) 
         -> exists j ρ, (j,[ρ]) <sc P /\ (k,[µ]) <sc (linker j, c linker j ρ).
  Proof using Hc.
    intros (l' & r' & H1 & H2).
    apply comp_in_inv in H1 as (l & ρ & r & a & b & H3 & H4 & H5 & H6).
    exists (length l+fst P), ρ; split.
    + destruct P as (sP,cP); simpl in *.
      exists l, r; split; auto; lia.
    + exists a, b; split; auto.
      rewrite H2, H5, app_length, plus_assoc; f_equal.
      rewrite comp_length.
      rewrite (linker_app _ _ H3); lia.
  Qed.

  Fact linker_code_start : linker (code_start P) = i.
  Proof. apply (linker_app nil (snd P)); auto. Qed.
  
  Fact linker_middle ll x mm : snd P = ll++x::mm -> linker (length ll+fst P) = lsum ll+i.
  Proof. apply linker_app. Qed.
  
  Fact linker_code_end : linker (code_end P) = lsum (snd P)+i.
  Proof.
    unfold code_end; rewrite plus_comm.
    apply (linker_app _ nil), app_nil_end.
  Qed.
  
   Fact linker_out_code j : err < i \/ length_compiler (snd P) + i <= err 
                        -> out_code j P -> out_code (linker j) (i,compiler).
  Proof using Hc.
    intros H1 H2.
    red in H2.
    destruct (eq_nat_dec j (code_end P)) as [ H | H ].
    rewrite H, linker_code_end; simpl.
    rewrite compiler_length; lia.
    rewrite linker_err_code.
    simpl; rewrite compiler_length; lia.
    simpl in H2, H; lia.
  Qed.

  Fact linker_out_err j : err = lsum (snd P) + i -> out_code j P -> linker j = err.
  Proof.
    intros H1 H2.
    destruct (eq_nat_dec j (code_end P)) as [ H | H ].
    + rewrite H1, H; unfold code_end.
      rewrite plus_comm, linker_app with (mm := nil); auto.
      rewrite <- app_nil_end; auto.
    + apply linker_err_code; red in H2; unfold code_end, code_start in *; lia.
  Qed.

End linker.

Section compiler_syntactic.

  Variable (X Y : Type)
           (c : (nat -> nat) -> nat -> X -> list Y) (* instruction compiler w.r.t. a given linker & a position *)
           (lc : X -> nat)                          (* compiled code length does not depend on linker or position *)
           .

  Record compiler_syntactic := MkCompSynt {
    cs_link     : (nat*list X) -> nat -> nat -> nat;
    cs_code     : (nat*list X) -> nat -> list Y;
    cs_fst      : forall P i, cs_link P i (fst P) = i;
    cs_in       : forall P i j, in_code j P -> in_code  (cs_link P i j) (i,cs_code P i); 
    cs_next     : forall P i j ρ, (j,[ρ]) <sc P -> cs_link P i (1+j) = lc ρ + cs_link P i j;
    cs_out      : forall P i j, out_code j P -> cs_link P i j = code_end (i,cs_code P i);
    cs_mono     : forall P i j k, code_start P <= j -> j <= k -> k < code_end P -> cs_link P i j <= cs_link P i k;
    cs_subcode    : forall P i j ρ, (j,[ρ]) <sc P -> (cs_link P i j, c (cs_link P i) j ρ) <sc (i,cs_code P i);
    cs_subcode_inv : forall P i k µ, (k,[µ]) <sc (i,cs_code P i) 
                           -> exists j ρ, (j,[ρ]) <sc P /\ (k,[µ]) <sc (cs_link P i j, c (cs_link P i) j ρ)
  }.

  (* In such a compiler_syntatic, the linker cannot give a (jump) value in the interval ] lnk k; lnk (1+k) [ *)

  Fact cs_not_between (gc : compiler_syntactic) P i j k : cs_link gc P i j <= cs_link gc P i k \/ cs_link gc P i (1+k) <= cs_link gc P i j.
  Proof.
    destruct gc as [ link code H1 H2 H3 H4 H5 H6 H7 ]; simpl.
    destruct (in_out_code_dec k P) as [ K | K ].
    + destruct (in_out_code_dec j P) as [ J | J ].
      * destruct (le_lt_dec j k) as [ G1 | G1 ]; [ left | right]; apply H5; red in K, J; lia.
      * apply H4 with (i := i) in J.
        destruct (in_out_code_dec (S k) P) as [ H' | H' ].
        - apply H2 with (i := i) in H'; red in H'; try lia.
        - apply H4 with (i := i) in H'; lia.
    + apply H4 with (i := i) in K.
      destruct (in_out_code_dec j P) as [ J | J ].
      * apply H2 with (i := i) in J; red in J; lia.
      * apply H4 with (i := i) in J; lia.
  Qed.

  Hypotheses (Hc1 : forall x, 1 <= lc x) 
             (Hc2 : forall f n x, length (c f n x) = lc x).

  Section generic_syntactic_compiler.

    Implicit Type P : nat*list X.

    Let err P iQ  := iQ+length_compiler lc (snd P).
    Let link P iQ := linker lc P iQ (err P iQ).
    Let code P iQ := compiler c lc P iQ (err P iQ).

    Local Fact fst_ok : forall P i, link P i (fst P) = i.
    Proof. intros [] ?; apply linker_code_start. Qed.

    Local Fact out_ok : forall P i j, out_code j P -> link P i j = code_end(i,code P i).
    Proof using Hc2.
      intros (iP,cP) iQ j H.
      unfold link, code_end.
      rewrite linker_out_err; unfold err; simpl; auto.
      * unfold code; rewrite compiler_length; auto.
      * lia.
    Qed.

    Theorem generic_syntactic_compiler : compiler_syntactic.
    Proof using Hc1 Hc2.
      exists link code; auto.
      + apply fst_ok.
      + intros Hlc P i j; now apply linker_in_code.
      + intros ? ? ? ? Hρ; apply compiler_subcode with (1 := Hc2) (2 := Hρ).
      + apply out_ok.
      + intros; apply linker_mono; try assumption.
        unfold code_end in *; lia.
      + intros ? ? ? ? Hρ; apply compiler_subcode with (1 := Hc2) (2 := Hρ).
      + intros; apply compiler_subcode_inv; auto.
    Qed.

  End generic_syntactic_compiler.

End compiler_syntactic.

Print compiler_syntactic.
Check generic_syntactic_compiler.


