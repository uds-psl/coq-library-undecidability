(* From Undecidability Require Import Combinators.Combinators Multi Basic.Mono TMTac. *)
From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import ArithPrelim.
From Undecidability Require Import TM.Compound.Shift.
From Undecidability Require Import TM.Util.VectorPrelim.

From Undecidability Require Import EncodeTapes TM.Util.VectorPrelim.
Require Import FunInd.


Local Set Printing Coercions.

(* Avoid using [Vector.to_list], because it doesn't [cbn] good. Use [vector_to_list] instead. *)
Local Arguments Vector.to_list {A n} (!v).

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.



Lemma removelast_cons (X : Type) (xs : list X) (x : X) :
  xs <> nil ->
  removelast (x :: xs) = x :: removelast xs.
Proof.
  destruct xs as [ | x' xs']; cbn.
  - congruence.
  - intros _. auto.
Qed.


(* TODO: ~> somewhere else *)
Lemma vector_to_list_inj (X : Type) (n : nat) (xs ys : Vector.t X n) :
  vector_to_list xs = vector_to_list ys -> xs = ys.
Proof.
  revert ys. induction xs as [ | x n xs IH]; intros; cbn in *.
  - destruct_vector. reflexivity.
  - destruct_vector. cbn in *. inv H. f_equal. auto.
Qed.


Section Fin.

  Global Coercion fin_to_nat (n : nat) (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).
  Global Set Printing Coercions.

  Lemma fin_to_nat_lt (n : nat) (i : Fin.t n) : fin_to_nat i < n.
  Proof. unfold fin_to_nat. destruct (Fin.to_nat i). cbn. auto. Qed.

  Lemma fin_to_nat_O (n : nat) :
    fin_to_nat (@Fin.F1 n) = 0.
  Proof. reflexivity. Qed.

  Lemma fin_to_nat_S (n : nat) (i : Fin.t n) :
    fin_to_nat (Fin.FS i) = S (fin_to_nat i).
  Proof.
    unfold fin_to_nat. destruct i as [ | n i].
    - cbn. reflexivity.
    - cbn in *. destruct (Fin.to_nat i) as [k ?]. cbn in *. reflexivity.
  Qed.

  Lemma fin_is_0 (n : nat) (i : Fin.t (S n)) :
    fin_to_nat i = 0 -> i = Fin0.
  Proof.
    intros H. pose proof fin_destruct_S i as [ (i'&->) | ->]; cbn in *; auto.
    rewrite fin_to_nat_S in H. lia.
  Qed.

  Lemma fin_is_1 (n : nat) (i : Fin.t (S (S n))) :
    fin_to_nat i = 1 -> i = Fin1.
  Proof.
    intros H. pose proof fin_destruct_S i as [ (i'&->) | ->]; cbn in *; auto.
    rewrite fin_to_nat_S in H. inv H. now apply fin_is_0 in H1 as ->.
  Qed.

  Lemma fin_is_2 (n : nat) (i : Fin.t (S (S (S n)))) :
    fin_to_nat i = 1 -> i = Fin1.
  Proof.
    intros H. pose proof fin_destruct_S i as [ (i'&->) | ->]; cbn in *; auto.
    rewrite fin_to_nat_S in H. inv H. now apply fin_is_0 in H1 as ->.
  Qed.
      

  Fixpoint finMax (n : nat) {struct n} : n <> 0 -> Fin.t n.
  Proof.
    destruct n as [ | n'].
    - abstract congruence.
    - decide (n' = 0) as [ H | H]. (* [destruct] makes troubles here *)
      + intros _. apply Fin.F1.
      + intros _. apply Fin.FS. apply (finMax n'). auto.
  Defined. (* because definition *)

  Definition finMax' (n : nat) : Fin.t (S n).
  Proof.
    apply finMax. apply Nat.neq_succ_0.
  Defined. (* because definition *)

  Lemma finMax_ext (n : nat) (H1 H2 : n <> 0) : finMax H1 = finMax H2.
  Proof.
    induction n as [ | n' IH].
    - congruence.
    - cbn. decide (n' = 0) as [H | H]; f_equal.
  Qed.

  Lemma finMax_val (n : nat) (H : n <> 0) : fin_to_nat (finMax H) = n - 1.
  Proof.
    unfold fin_to_nat. induction n as [ | n' IH ].
    - congruence.
    - cbn. decide (n' = 0) as [ -> | H']; cbn.
      + reflexivity.
      + replace (n' - 0) with n' by lia.
        specialize IH with (H := H').
        destruct (Fin.to_nat (finMax H')) as [k ?]; cbn in *. lia.
  Qed.

  (* Arguments finMax (n) H : clear implicits. *)

  (* Compute finMax (ltac:(congruence) : 1 <> 0). *)
  (* Compute finMax (ltac:(congruence) : 10 <> 0). *)
  (* Compute finMax' 99. *)

  Definition finMin (n : nat) : n <> 0 -> Fin.t n.
  Proof.
    refine (match n as n' return n' <> 0 -> Fin.t n' with
            | 0 => fun H => False_rec _ _
            | S n' => fun _ => Fin.F1
            end); auto.
  Defined. (* because definition *)

  Lemma finMin_O (n : nat) (H : S n <> 0) : finMin H = Fin.F1.
  Proof. cbn. reflexivity. Qed.

  Lemma finMin_ext (n : nat) (H1 H2 : n <> 0) : finMin H1 = finMin H2.
  Proof.
    destruct n.
    - congruence.
    - auto.
  Qed.

  Lemma finMin_val (n : nat) (H : n <> 0) : fin_to_nat (finMin H) = 0.
  Proof.
    unfold fin_to_nat. destruct n as [ | n'].
    - congruence.
    - cbn. reflexivity.
  Qed.

  Lemma finSucc_help (i : Fin.t 1) : i = Fin0.
  Proof. now destruct_fin i. Qed.


  Lemma finSucc_help' (n : nat) (i1 i2 : Fin.t n) :
    Fin.FS i1 <> Fin.FS i2 -> i1 <> i2.
  Proof. now intros H1 ->. Qed.

  Fixpoint finSucc (n : nat) (i : Fin.t n) {struct n} : forall (H : n <> 0), i <> finMax H -> Fin.t n.
  Proof.
    destruct n as [ | n'].
    - intros. abstract congruence.
    - cbn. decide (n' = 0) as [ HDec | HDec]; cbn.
      + intros _ Hi. exfalso. apply Hi. subst. apply finSucc_help.
      + intros _.
        revert n' i HDec. refine (@Fin.caseS (fun n' i => forall (HDec : n' <> 0), i <> Fin.FS (finMax HDec) -> Fin.t (S n')) _ _).
        * intros. apply Fin.FS. apply finMin. apply HDec.
        * intros. apply Fin.FS. eapply finSucc. eapply finSucc_help'. apply H.
  Defined. (* because definition *)

  Definition finSucc' (n : nat) (i : Fin.t (S n)) (H : i <> finMax' n) : Fin.t (S n).
  Proof. unshelve eapply finSucc with (i := i). apply Nat.neq_succ_0. apply H. Defined. (* because definition *)

  (* Compute @finSucc 5 Fin0 _ _. *)
  (* Compute finSucc' (_ : Fin4 <> finMax' 10). *)


  Fixpoint finSucc_opt (n : nat) (i : Fin.t n) {struct i} : option (Fin.t n).
  Proof.
    destruct i.
    - destruct n.
      + apply None.
      + apply Some. apply Fin.FS. apply Fin.F1.
    - destruct n.
      + destruct_fin i.
      + destruct (finSucc_opt _ i) as [ rec | ].
        * apply Some. apply Fin.FS. apply rec.
        * apply None.
  Defined. (* because definition *)

  (* Compute eq_refl : @finSucc_opt 1 Fin0 = None. *)
  (* Compute eq_refl : @finSucc_opt 2 Fin0 = Some Fin1. *)
  (* Compute eq_refl : @finSucc_opt 2 Fin1 = None. *)
  (* Compute eq_refl : @finSucc_opt 3 Fin1 = Some Fin2. *)
  (* Compute eq_refl : @finSucc_opt 3 Fin0 = Some Fin1. *)
  (* Compute eq_refl : @finSucc_opt 8 Fin7 = None. *)
  (* Compute eq_refl : @finSucc_opt 9 Fin7 = Some Fin8. *)

  Lemma finSucc_opt_Some (n : nat) (i : Fin.t n) :
    S (fin_to_nat i) < n ->
    exists i', finSucc_opt i = Some i'.
  Proof.
    induction i; intros; cbn in *.
    - destruct n. lia. eauto.
    - destruct n; cbn. lia.
      rewrite !fin_to_nat_S in *.
      spec_assert IHi as (i'&IH) by lia. rewrite IH. eauto.
  Qed.

  Lemma finSucc_opt_Some' (n : nat) (i i' : Fin.t n) :
    finSucc_opt i = Some i' ->
    fin_to_nat i' = S (fin_to_nat i).
  Proof.
    revert i'. induction i; cbn; intros.
    - destruct n; inv H. cbn. reflexivity.
    - destruct n; cbn in *. destruct_fin i.
      destruct (finSucc_opt i) as [ i'' | ] eqn:E; inv H.
      rewrite fin_to_nat_S. rewrite IHi; auto.
      now rewrite fin_to_nat_S.
  Qed.

  Lemma finSucc_opt_None (n : nat) (i : Fin.t n) :
    S (fin_to_nat i) = n ->
    finSucc_opt i = None.
  Proof.
    induction i; intros; cbn in *.
    - inv H. reflexivity.
    - rewrite fin_to_nat_S in *. inv H. spec_assert IHi by assumption.
      destruct n; cbn. lia. rewrite IHi. reflexivity.
  Qed.

  Lemma finSucc_opt_None' (n : nat) (i : Fin.t n) :
    finSucc_opt i = None ->
    S (fin_to_nat i) = n.
  Proof.
    induction i; cbn; intros.
    - destruct n; now inv H.
    - destruct n. destruct_fin i.
      destruct (finSucc_opt i) as [ i' | ]; inv H.
      now rewrite fin_to_nat_S, IHi.
  Qed.




  Definition finMin_opt (n : nat) : option (Fin.t n).
  Proof.
    destruct n.
    - apply None.
    - apply Some. apply Fin.F1.
  Defined. (* because definition *)

  Lemma finMin_opt_None (n : nat) :
    finMin_opt n = None -> n = 0.
  Proof. destruct n; cbn; congruence. Qed.

  Lemma finMin_opt_Some (n : nat) i :
    finMin_opt n = Some i -> exists n', n = S n'.
  Proof. destruct n; cbn; intros H; inv H; eauto. Qed.

  Lemma finMin_opt_Some_val (n : nat) i :
    finMin_opt n = Some i -> fin_to_nat i = 0.
  Proof. destruct n; cbn; intros H; inv H; auto. Qed.

  Lemma finSucc_correct (n : nat) (i : Fin.t n) (H1 : n <> 0) (H2 : i <> finMax H1) :
    fin_to_nat (finSucc H2) = S (fin_to_nat i).
  Proof.
     revert i H1 H2. induction n as [ | n' IH]; intros; cbn in *.
    - congruence.
    - decide (n' = 0) as [-> | HDec]; cbn.
      + exfalso. apply H2. apply finSucc_help.
      + pose proof fin_destruct_S i as [ (i'&->) | -> ]; cbn -[Fin.to_nat]; swap 1 2.
        * change (S (proj1_sig (Fin.to_nat Fin0))) with 1.
          rewrite fin_to_nat_S. f_equal. rewrite finMin_val. reflexivity.
        * rewrite !fin_to_nat_S. f_equal. now rewrite IH.
  Qed.


End Fin.



Fixpoint map_vect_list (X Y : Type) (f : X -> Y -> X) (n : nat) (vs : Vector.t Y n) (ls : list X) {struct ls} : list X :=
  match ls with
  | nil => nil
  | x :: ls' =>
    match vs with
    | [| |] => ls
    | y ::: vs' =>
      f x y :: map_vect_list f vs' ls'
    end
  end.


Lemma map_vect_list_length (X Y : Type) (f : X -> Y -> X) (n : nat) (vs : Vector.t Y n) (ls : list X) :
  length (map_vect_list f vs ls) = length ls.
Proof.
  revert n vs. induction ls as [ | x ls IH]; cbn; intros.
  - reflexivity.
  - destruct vs as [ | y n vs]; cbn; f_equal; auto.
Qed.


Lemma map_vect_list_app (X Y : Type) (f : X -> Y -> X) (n : nat) (vs : Vector.t Y n) (ls : list X)
      (x : X) (i : Fin.t n) :
  fin_to_nat i = length ls ->
  map_vect_list f vs (ls ++ [x]) =
  map_vect_list f vs ls ++ [f x vs[@i]].
Proof.
  revert n vs i. induction ls as [ | x' ls IH]; cbn; intros.
  - destruct vs. destruct_fin i.
    enough (i = Fin.F1) as -> by auto.
    pose proof fin_destruct_S i as [ (i'&->) | ]; cbn in *; auto.
    rewrite fin_to_nat_S in *. lia.
  - destruct vs as [ | v n vs]; cbn in *.
    + destruct_fin i.
    + f_equal.
      pose proof fin_destruct_S i as [ (i'&->) | -> ]; cbn in *.
      * rewrite fin_to_nat_S in *. apply IH. lia.
      * lia.
Qed.


Lemma map_vect_list_eq (X Y : Type) (n1 : nat) (f : X -> Y -> X) (vs : Vector.t Y n1) (xs : Vector.t X n1) :
  map_vect_list f vs (vector_to_list xs) = vector_to_list (Vector.map2 f xs vs).
Proof.
  revert xs. induction vs as [ | v n1 vs IH]; intros; cbn in *.
  - destruct_vector. cbn. reflexivity.
  - pose proof destruct_vector_cons xs as (x'&xs'&->). cbn.
    f_equal. auto.
Qed.


Lemma destruct_tapes1 (sig : Type) (t : tapes sig 1) :
  exists t', t = [| t' |].
Proof. destruct_tapes. eauto. Qed.


Section BookKeepingForRead.

  Variable sig : Type.

  Set Default Proof Using "Type".

  Fixpoint knowsFirstSymbols {n' : nat} (readSymbols : Vector.t (option sig) n') (tps : list (tape sig)) {struct readSymbols} : Prop :=
    match readSymbols, tps with
    | Vector.nil _,  nil => True /\ True /\ True
    | Vector.nil _, _::_ => True /\ True (* to much tapes *)
    | x ::: readSymbols, nil => True (* list of tapes is too big, must not happen *)
    | x ::: readSymbols', tp :: tps' =>
      current tp = x /\ knowsFirstSymbols readSymbols' tps'
    end.

  Lemma knowsFirstSymbols_nil {n : nat} (readSymbols : Vector.t (option sig) n) :
    knowsFirstSymbols readSymbols nil.
  Proof.
    destruct n.
    - destruct_vector. cbn. tauto.
    - destruct_vector. cbn. tauto.
  Qed.

  Definition insertKnownSymbol {n : nat} (readSymbols : Vector.t (option sig) n) (i : Fin.t n) (s : option sig) : Vector.t (option sig) n :=
    Vector.replace readSymbols i s.

  Fixpoint insertKnownSymbols {n : nat} (readSymbols : Vector.t (option sig) n) (i : Fin.t n) (newSymbols : list (option sig)) :
    Vector.t (option sig) n :=
    match newSymbols with
    | nil => readSymbols
    | s :: newSymbols' =>
      match finSucc_opt i with
      | Some i' => insertKnownSymbols (insertKnownSymbol readSymbols i s) i' newSymbols'
      | None => insertKnownSymbol readSymbols i s
      end
    end.
  

  Lemma insertKnownSymbol_correct (n : nat) (readSymbols : Vector.t (option sig) n) (i : Fin.t n) tps tp :
    length tps = fin_to_nat i ->
    knowsFirstSymbols readSymbols tps ->
    knowsFirstSymbols (insertKnownSymbol readSymbols i (current tp)) (tps ++ [tp]).
  Proof.
    revert i tps tp. induction readSymbols as [ | x n readSymbols IH]; intros; cbn in *.
    - destruct_fin i.
    - pose proof fin_destruct_S i as [ ( i0 & -> ) | -> ]; cbn in *.
      + rewrite fin_to_nat_S in *. destruct tps; cbn in *; inv H. destruct H0 as [H0 H0']. split; auto.
      + destruct tps; cbn in *; inv H. split; auto. apply knowsFirstSymbols_nil.
  Qed.
        
  Lemma insertKnownSymbols_correct (n : nat) (readSymbols : Vector.t (option sig) n) (i : Fin.t n) tps1 tps2 :
    length tps1 = fin_to_nat i ->
    length tps1 + length tps2 = n ->
    knowsFirstSymbols readSymbols tps1 ->
    knowsFirstSymbols (insertKnownSymbols readSymbols i (map (@current _) tps2)) (tps1 ++ tps2).
  Proof.
    revert n i tps1 readSymbols. induction tps2 as [ | tp' tps2 IH]; cbn; intros.
    - now rewrite app_nil_r.
    - subst.
      destruct (finSucc_opt i) as [ i' | ] eqn:E.
      + pose proof finSucc_opt_Some' E as E'.
        rewrite app_comm_cons'. apply IH; simpl_list; cbn. lia. lia.
        apply insertKnownSymbol_correct; auto.
      + apply finSucc_opt_None' in E.
        assert (| tps2 | = 0) by lia.
        destruct tps2; cbn in *; inv H0.
        apply insertKnownSymbol_correct; auto.
  Qed.


  (*
  H : knowsFirstSymbols
        (insertKnownSymbols (current tp ::: Vector.const None n) Fin0
           (map (current (sig:=sig)) (tp :: vector_to_list T))) ([] ++ tp :: vector_to_list T)
  ============================
  insertKnownSymbols (current tp ::: Vector.const None n) Fin0 (vector_to_list (current_chars T)) =
  current_chars (tp ::: T)
*)

  Lemma knowsFirstSymbols_all n (tps : list (tape sig)) (symbols : Vector.t (option sig) n) :
    length tps = n ->
    knowsFirstSymbols symbols tps ->
    vector_to_list symbols = map (@current _) tps.
  Proof.
    revert tps. induction symbols; cbn; intros.
    - destruct tps; cbn in *; auto.
    - destruct tps; cbn in *; inv H. destruct H0 as [ <- ?]. f_equal. auto.
  Qed.

  Lemma knowsFirstSymbols_all' n (T : tapes sig n) (symbols : Vector.t (option sig) n) :
    knowsFirstSymbols symbols (vector_to_list T) ->
    symbols = current_chars T.
  Proof.
    induction T as [ | tp n T IH]; intros; cbn in *.
    - destruct_vector. reflexivity.
    - destruct_vector. unfold current_chars. cbn in *. destruct H as [ <- H]. f_equal. auto.
  Qed.



  Lemma insertKnownSymbols_correct_cons n (T : tapes sig (S n)) (min minSucc : Fin.t (S n)) :
    fin_to_nat min = 0 ->
    fin_to_nat minSucc = 1 ->
    insertKnownSymbols (insertKnownSymbol (Vector.const None (S n)) min (current (Vector.hd T))) minSucc
                       (map (@current _) (vector_to_list (Vector.tl T))) = 
    current_chars T.
  Proof.
    intros HMin_val HMinSucc_val.
    unshelve epose proof @insertKnownSymbols_correct (S n) (Vector.const None (S n)) min nil (vector_to_list T) _ _ _.
    - cbn. auto.
    - cbn. apply vector_to_list_length.
    - cbn. tauto.
    - cbn in *. apply knowsFirstSymbols_all' in H. rewrite <- H.
      assert (min = Fin.F1) as -> by now apply fin_is_0. cbn.
      destruct n as [ | n'].
      + destruct_fin minSucc; auto. lia.
      + assert (minSucc = Fin.FS Fin.F1) as -> by now apply fin_is_1.
        destruct_tapes. cbn. auto.
  Qed.
      
    
  (*
  E_val : fin_to_nat min = 0
  E2_val : fin_to_nat minSucc = 1
  minSucc : Fin.t (S n')
  ============================
  insertKnownSymbols (insertKnownSymbol (Vector.const None (S n')) min (current (Vector.hd T))) minSucc
    (map (current (sig:=eqType_X (type sig))) (vector_to_list (Vector.tl T))) = 
  current_chars T
  *)
  
End BookKeepingForRead.




Section ToSingleTape.

  Variable (sig F : finType).
  Variable n : nat.
  (* Hypothesis (nNeq0 : n <> 0). (* This really makes no sense for [0] tapes. *) *)
  Notation nMax := (finMax' n).
  Local Arguments finMax' : simpl never.

  Notation sigSim := (FinType(EqType(boundary + sigList (sigTape sig)))).

  Implicit Types (T : tapes sig n).

  Definition contains_tapes (t : tape sigSim) T :=
    t = midtape nil (inl START) (map inr (encode_tapes T) ++ [inl STOP]).
  Notation "t ≃ T" := (contains_tapes t T) (at level 70, no associativity).


  Hypothesis pM : pTM sig F n.



  (* Go to the current symbol of the selected tape *)
  Section GoToCurrent.

    Definition atStart (t : tape sigSim) (tps : list (tape sig)) : Prop :=
      t = midtape nil (inl START) (map inr (encode_list _ tps) ++ [inl STOP]).

    Definition atCons (t : tape sigSim) (tps1 tps2 : list (tape sig)) (tp : tape sig) : Prop :=
      t = midtape (map inr (rev (removelast (encode_list _ tps1))) ++ [inl START])
                  (inr (sigList_cons))
                  (map inr (map sigList_X (encode_tape tp)) ++ map inr (encode_list _ tps2) ++ [inl STOP]).

    Definition atNil (t : tape sigSim) (tps : list (tape sig)) : Prop :=
      t = midtape (map inr (rev (removelast (encode_list _ tps))) ++ [inl START]) (inr (sigList_nil)) [inl STOP].


    Definition atCons_current_niltape (t : tape sigSim) (tps1 tps2 : list (tape sig)) : Prop :=
      t = midtape
            (inr (sigList_cons) :: map inr (rev (removelast (encode_list _ tps1))) ++ [inl START])
            (inr (sigList_X NilBlank))
            (map inr (encode_list _ tps2) ++ [inl STOP]).

    Definition atCons_current_leftof (t : tape sigSim) (tps1 tps2 : list (tape sig)) (r : sig) (rs : list sig) :=
      t = midtape
            (inr (sigList_cons) :: map inr (rev (removelast (encode_list _ tps1))) ++ [inl START])
            (inr (sigList_X (LeftBlank true)))
            (inr (sigList_X (UnmarkedSymbol r)) ::
                 map (fun s => inr (sigList_X (UnmarkedSymbol s))) rs ++ inr (sigList_X (RightBlank false)) ::
                 map inr (encode_list _ tps2) ++ [inl STOP]).

    Definition atCons_current_midtape (t : tape sigSim) (tps1 tps2 : list (tape sig)) (ls : list sig) (m : sig) (rs : list sig) :=
      t = midtape
            (map (fun s => inr (sigList_X (UnmarkedSymbol s))) ls ++ (* [ls] is reversed twice *)
                 inr (sigList_X (LeftBlank false)) :: inr (sigList_cons) :: map inr (rev (removelast (encode_list _ tps1))) ++ [inl START])
            (inr (sigList_X (MarkedSymbol m)))
            (map (fun s => inr (sigList_X (UnmarkedSymbol s))) rs ++ inr (sigList_X (RightBlank false)) ::
                 map inr (encode_list _ tps2) ++ [inl STOP]).

    Definition atCons_current_rightof (t : tape sigSim) (tps1 tps2 : list (tape sig)) (l :sig) (ls : list sig) :=
      t = midtape
            (inr (sigList_X (UnmarkedSymbol l)) ::
                 map (fun s => inr (sigList_X (UnmarkedSymbol s))) ls ++ (* [ls] is reversed twice *)
                 inr (sigList_X (LeftBlank false)) :: inr (sigList_cons) :: map inr (rev (removelast (encode_list _ tps1))) ++ [inl START])
            (inr (sigList_X (RightBlank true)))
            (map inr (encode_list _ tps2) ++ [inl STOP]).

    Definition atCons_current (t : tape sigSim) (tps1 tps2 : list (tape sig)) (tp : tape sig) :=
      match tp with
      | niltape _ => atCons_current_niltape t tps1 tps2
      | leftof r rs => atCons_current_leftof t tps1 tps2 r rs
      | midtape ls m rs => atCons_current_midtape t tps1 tps2 ls m rs
      | rightof l ls => atCons_current_rightof t tps1 tps2 l ls
      end.

    Definition tape_dir (t : tape sig) : option move :=
      match t with
      | niltape _ => None
      | leftof _ _ => Some Lmove
      | midtape _ _ _ => Some Nmove
      | rightof _ _ => Some Rmove
      end.

    Definition isMarked' (s : sigSim) : bool :=
      match s with
      | inr (sigList_X s) => isMarked s
      | _ => false
      end.


    Definition IsCons_Rel : pRel sigSim bool 1 :=
      fun tin '(yout, tout) =>
        (forall tps1 tps2 tp,
            atCons tin[@Fin0] tps1 tps2 tp ->
            atCons tout[@Fin0] tps1 tps2 tp /\
            yout = true) /\
        (forall tps,
            atNil tin[@Fin0] tps ->
            atNil tout[@Fin0] tps /\
            yout = false).

    Definition IsCons : pTM sigSim bool 1 :=
      Switch ReadChar
             (fun (s : option sigSim) =>
                match s with
                | Some (inr (sigList_cons)) => Return Nop true
                | Some (inr (sigList_nil)) => Return Nop false
                | _ => Return Nop default
                end).

    Definition IsCons_steps := 2.

    Lemma IsCons_Sem : IsCons ⊨c(IsCons_steps) IsCons_Rel.
    Proof.
      unfold IsCons_steps. eapply RealiseIn_monotone.
      { unfold IsCons. TM_Correct. }
      { Unshelve. 4-5: reflexivity. all: reflexivity. }
      {
        intros tin (yout, tout) H. split.
        { (* [cons] case *) intros tps1 tps2 tp HCons. unfold atCons in *. TMSimp. auto. }
        { (* [nil] case *) intros tps HNil. unfold atNil in *. TMSimp. auto. }
      }
    Qed.

    Definition GoToCurrent_Rel : pRel sigSim (option move) 1 :=
      fun tin '(yout, tout) =>
        forall (tps1 tps2 : list (tape sig)) (tp : tape sig),
          atCons tin[@Fin0] tps1 tps2 tp ->
          atCons_current tout[@Fin0] tps1 tps2 tp /\
          yout = tape_dir tp.


    Definition GoToCurrent : pTM sigSim (option move) 1 :=
      MoveToSymbol isMarked' id;;
      Switch ReadChar
      (fun (c : option sigSim) =>
         match c with
         | Some (inr (sigList_X (RightBlank true))) => Return Nop (Some Rmove)
         | Some (inr (sigList_X (LeftBlank true))) => Return Nop (Some Lmove)
         | Some (inr (sigList_X (MarkedSymbol _))) => Return Nop (Some Nmove)
         | Some (inr (sigList_X NilBlank)) => Return Nop (None)
         | _ => Return Nop None
         end).

    Lemma GoToCurrent_Realise : GoToCurrent ⊨ GoToCurrent_Rel.
    Proof.
      eapply Realise_monotone.
      { unfold GoToCurrent. TM_Correct. }
      {
        intros tin (yout, tout) H. intros tps1 tps2 tp HCons. unfold atCons in *. TMSimp.
        rename H1 into H.
        destruct tp as [ | r rs | l ls | ls m rs]; cbn in *; TMSimp.
        - (* tp = niltape *)
          do 2 ( rewrite MoveToSymbol_Fun_equation in *; cbn in * ). TMSimp.
          split; eauto. hnf. reflexivity.
        - (* tp = leftof r rs *) 
          do 2 ( rewrite MoveToSymbol_Fun_equation in *; cbn in * ). TMSimp.
          split; auto. hnf. cbn. f_equal. rewrite !List.map_map, !map_app, <- !app_assoc, !List.map_map. cbn. reflexivity.
        - (* tp = rightof l ls *)
          replace (inr (sigList_X (LeftBlank false)) ::
                       map inr (map sigList_X (map UnmarkedSymbol (rev ls) ++ [UnmarkedSymbol l; RightBlank true])) ++
                       map inr (encode_list (Encode_tape (eqType_X (type sig))) tps2) ++ [inl STOP]) with
              ((inr (sigList_X (LeftBlank false)) :: map inr (map sigList_X (map UnmarkedSymbol (rev ls) ++ [UnmarkedSymbol l])))
                 ++ inr (sigList_X (RightBlank true)) :: (map inr (encode_list (Encode_tape (eqType_X (type sig))) tps2) ++ [inl STOP]))
            in H by (now simpl_list; cbn; rewrite <- !app_assoc).
          rewrite MoveToSymbol_correct_midtape in H; cbn; auto.
          + cbn in *. TMSimp. split; auto. hnf. f_equal.
            rewrite !map_id, !List.map_map. cbv [id].
            rewrite !map_app; cbn. rewrite !List.map_map. rewrite rev_app_distr. cbn. rewrite !map_rev, rev_involutive, <- app_assoc. reflexivity.
          + rewrite !map_app, !List.map_map. cbn. intros ? [<- | [(?&<-&?)%in_map_iff | [<- | ?]] % in_app_iff ]; cbn; auto.
        - (* tp = midtape ls m rs *)
          replace (inr (sigList_X (LeftBlank false)) ::
                       map inr (map sigList_X (map UnmarkedSymbol (rev ls) ++ MarkedSymbol m :: map UnmarkedSymbol rs ++ [RightBlank false])) ++ map inr (encode_list (Encode_tape (eqType_X (type sig))) tps2) ++ [inl STOP]) with
              ((inr (sigList_X (LeftBlank false)) :: map inr (map sigList_X (map UnmarkedSymbol (rev ls))))
                 ++ inr (sigList_X (MarkedSymbol m)) ::
                 (map inr (map sigList_X (map UnmarkedSymbol rs ++ [RightBlank false])) ++
                      map inr (encode_list (Encode_tape (eqType_X (type sig))) tps2) ++ [inl STOP])) in H.
          rewrite MoveToSymbol_correct_midtape in H; cbn; auto.
          + cbn in *. TMSimp. split; auto. hnf.
            rewrite !map_id, !List.map_map. cbv [id].
            rewrite !map_app; cbn. rewrite !List.map_map, <- !app_assoc. rewrite map_rev, rev_involutive. f_equal.
          + rewrite !List.map_map. intros ? [ <- | (?&<-&?) % in_map_iff]; cbn; auto.
          + simpl_list. cbn. f_equal. f_equal. f_equal. rewrite !map_app, <- !app_assoc. cbn. f_equal.
      }
    Qed.


    Definition GoToCurrent_steps' (tp : tape sig) :=
      match tp with
       | niltape _ => 8
       | leftof r rs => 8
       | rightof l ls => 16 + 4 * length ls
       | midtape ls m rs => 16 + 4 * length ls
       end.

    Definition GoToCurrent_steps (tp : tape sig) :=
       GoToCurrent_steps' tp + 3.

    Definition GoToCurrent_T : tRel sigSim 1 :=
      fun tin k => exists tps1 tps2 tp, atCons tin[@Fin0] tps1 tps2 tp /\ GoToCurrent_steps tp <= k.

    Lemma GoToCurrent_Terminates : projT1 GoToCurrent ↓ GoToCurrent_T.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold GoToCurrent. TM_Correct. }
      { intros tin k (tps1&tps2&tp&HCons&Hk). unfold GoToCurrent_steps in Hk.
        exists (GoToCurrent_steps' tp), 2. cbn.
        repeat split. 2: lia.
        {
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; hnf in HCons; TMSimp.
          - (* [tp = niltape] *) do 2 ( rewrite MoveToSymbol_steps_equation; cbn in * ). reflexivity.
          - (* [tp = leftof r rs] *) do 2 ( rewrite MoveToSymbol_steps_equation; cbn in * ). reflexivity.
          - (* [tp = rightof l ls] *)
            replace (inr (sigList_X (LeftBlank false)) ::
                         map inr (map sigList_X (map UnmarkedSymbol (rev ls) ++ [UnmarkedSymbol l; RightBlank true])) ++
                         map inr (encode_list (Encode_tape (eqType_X (type sig))) tps2) ++ [inl STOP]) with
                ((inr (sigList_X (LeftBlank false)) :: map inr (map sigList_X (map UnmarkedSymbol (rev ls) ++ [UnmarkedSymbol l])))
                   ++ inr (sigList_X (RightBlank true)) :: (map inr (encode_list (Encode_tape (eqType_X (type sig))) tps2) ++ [inl STOP]))
              by (now simpl_list; cbn; rewrite <- !app_assoc).
            rewrite MoveToSymbol_steps_midtape; cbn; auto.
            simpl_list. cbn. rewrite Nat.mul_succ_r. cbn. lia.
          - (* tp = midtape ls m rs *)
            replace (inr (sigList_X (LeftBlank false)) ::
                         map inr (map sigList_X (map UnmarkedSymbol (rev ls) ++ MarkedSymbol m :: map UnmarkedSymbol rs ++ [RightBlank false])) ++ map inr (encode_list (Encode_tape (eqType_X (type sig))) tps2) ++ [inl STOP]) with
                ((inr (sigList_X (LeftBlank false)) :: map inr (map sigList_X (map UnmarkedSymbol (rev ls))))
                   ++ inr (sigList_X (MarkedSymbol m)) ::
                   (map inr (map sigList_X (map UnmarkedSymbol rs ++ [RightBlank false])) ++
                        map inr (encode_list (Encode_tape (eqType_X (type sig))) tps2) ++ [inl STOP])).
            rewrite MoveToSymbol_steps_midtape; cbn; auto.
            + simpl_list. cbn. lia.
            + simpl_list. cbn. f_equal. f_equal. f_equal. rewrite !map_app, <- !app_assoc. cbn. f_equal.
        }
        { intros ? [] ?. exists 1, 0. repeat split. lia. lia. intros ? ? (->&->). destruct *; reflexivity. }
      }
    Qed.

  End GoToCurrent.


  Section GoToNext.

    Definition GoToNext_Rel : pRel sigSim bool 1 :=
      fun tin '(yout, tout) =>
        forall tps1 tps2 tp,
          atCons_current tin[@Fin0] tps1 tps2 tp ->
          match yout, tps2 with
          | true, tp' :: tps2' =>
            atCons tout[@Fin0] (tps1 ++ [tp]) tps2' tp'
          | false, nil =>
            atNil tout[@Fin0] (tps1 ++ [tp])
          | _, _ => False
          end.

    Definition isNilCons : sigSim -> bool :=
      fun s => match s with
            | inr sigList_nil => true
            | inr sigList_cons => true
            | _ => false
            end.

    Definition GoToNext : pTM sigSim bool 1 :=
      MoveToSymbol isNilCons id;; IsCons.

    Lemma GoToNext_Realise : GoToNext ⊨ GoToNext_Rel.
    Proof.
      eapply Realise_monotone.
      { unfold GoToNext. TM_Correct. eapply RealiseIn_Realise. apply IsCons_Sem. }
      {
        intros tin (yout, tout) H. intros tps1 tps2 tp HCons. unfold atCons_current in *. TMSimp.
        TMSimp. rename H1 into H.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; hnf in HCons; TMSimp; rename H into HNil, H0 into HCons.
        { (* [niltape] *)
          destruct tps2 as [ | tp' tps2']; cbn in *.
          - specialize (HNil (tps1 ++ [niltape _])). spec_assert HNil as [HNil ->]; auto.
            do 2 (rewrite MoveToSymbol_Fun_equation; cbn). hnf.
            cbv [id]. hnf. f_equal. rewrite encode_list_app. rewrite removelast_app by apply encode_list_neq_nil.
            cbn. rewrite rev_app_distr. cbn. f_equal.
          - specialize (HCons (tps1 ++ [niltape _]) tps2' tp'). spec_assert HCons as [HCons ->]; auto.
            do 2 (rewrite MoveToSymbol_Fun_equation; cbn).
            cbv [id]. hnf. f_equal.
            + rewrite encode_list_app; cbn. rewrite removelast_app by congruence.
              cbn. rewrite rev_app_distr. cbn. f_equal.
            + rewrite !List.map_map. rewrite !map_app, <- !app_assoc. now rewrite !List.map_map. }
        { (* [leftof r rs] *)
          destruct tps2 as [ | tp' tps2']; cbn in *.
          - specialize (HNil (tps1 ++ [leftof r rs])). spec_assert HNil as [HNil ->]; auto.
            rewrite app_comm_cons' with (a := inr (sigList_X (RightBlank false))).
            rewrite app_comm_cons with (a := inr (sigList_X (UnmarkedSymbol r))).
            rewrite MoveToSymbol_correct_midtape; cbn in *; auto.
            + rewrite !map_id; cbv [id]. hnf. f_equal.
              simpl_list. cbn. rewrite encode_list_app. cbn.
              rewrite !map_app. cbn. rewrite !removelast_app by congruence. rewrite !removelast_cons by congruence.
              rewrite removelast_cons.
              2: { intros H. symmetry in H. now apply app_cons_not_nil in H. }
              rewrite removelast_app by congruence. cbn. rewrite app_nil_r.
              rewrite rev_app_distr. cbn. rewrite <- !app_assoc.
              rewrite !rev_app_distr, <- !app_assoc. cbn. rewrite !map_rev.
              rewrite map_app, <- !app_assoc. cbn. rewrite !map_rev, !List.map_map. f_equal.
            + intros ? [ <- | [ (?&<-&?) % in_map_iff | [ <- | ] ] % in_app_iff ]; cbn; auto.
          - specialize (HCons (tps1 ++ [leftof r rs]) tps2' tp'). spec_assert HCons as [HCons ->]; auto.
            rewrite app_comm_cons' with (a := inr (sigList_X (RightBlank false))).
            rewrite app_comm_cons with (a := inr (sigList_X (UnmarkedSymbol r))).
            rewrite MoveToSymbol_correct_midtape; cbn in *; auto.
            + rewrite !map_id; cbv [id]. hnf. f_equal.
              * simpl_list. cbn. rewrite encode_list_app. cbn.
                rewrite !map_app. cbn. rewrite !removelast_app by congruence. rewrite !removelast_cons by congruence.
                rewrite removelast_cons.
                2: { intros H. symmetry in H. now apply app_cons_not_nil in H. }
                rewrite removelast_app by congruence. cbn. rewrite app_nil_r.
                rewrite rev_app_distr. cbn. rewrite <- !app_assoc.
                rewrite !rev_app_distr, <- !app_assoc. cbn. rewrite !map_rev.
                rewrite map_app, <- !app_assoc. cbn. rewrite !map_rev, !List.map_map. f_equal.
              * now simpl_list.
            + intros ? [ <- | [ (?&<-&?) % in_map_iff | [ <- | ] ] % in_app_iff ]; cbn; auto.
        }
        { (* [rightof l ls] *)
          destruct tps2 as [ | tp' tps2']; cbn in *.
          - specialize (HNil (tps1 ++ [rightof l ls])). spec_assert HNil as [HNil ->]; auto.
            do 2 (rewrite MoveToSymbol_Fun_equation; cbn).
            cbv [id]. hnf. f_equal.
            rewrite encode_list_app. cbn. rewrite removelast_app by congruence.
            rewrite !removelast_cons. 3: congruence.
            2: { intros H; symmetry in H; now apply app_cons_not_nil in H. }
            rewrite map_app, !List.map_map, <- !app_assoc. cbn.
            rewrite removelast_app by congruence. cbn.
            rewrite rev_app_distr; cbn. rewrite <- !app_assoc. cbn. rewrite !map_app, <- !app_assoc.
            rewrite !rev_app_distr. cbn. rewrite !map_rev, rev_involutive. rewrite !List.map_map. reflexivity.
          - specialize (HCons (tps1 ++ [rightof l ls]) tps2' tp'). spec_assert HCons as [HCons ->]; auto.
            do 2 (rewrite MoveToSymbol_Fun_equation; cbn).
            cbv [id]. hnf. f_equal.
            + rewrite encode_list_app. cbn. rewrite removelast_app by congruence.
              rewrite !removelast_cons. 3: congruence.
              2: { intros H; symmetry in H; now apply app_cons_not_nil in H. }
              rewrite map_app, !List.map_map, <- !app_assoc. cbn.
              rewrite removelast_app by congruence. cbn.
              rewrite rev_app_distr; cbn. rewrite <- !app_assoc. cbn. rewrite !map_app, <- !app_assoc.
              rewrite !rev_app_distr. cbn. rewrite !map_rev, rev_involutive. rewrite !List.map_map. reflexivity.
            + now simpl_list.
        }
        { (* [midtape ls m rs *)
          destruct tps2 as [ | tp' tps2']; cbn in *.
          - specialize (HNil (tps1 ++ [midtape ls m rs])). spec_assert HNil as [HNil ->]; auto.
            rewrite app_comm_cons' with (a := inr (sigList_X (RightBlank false))).
            rewrite MoveToSymbol_correct_midtape; cbn; auto.
            + cbn in *. TMSimp. rewrite map_id; cbv [id]. hnf. f_equal.
              rewrite encode_list_app. cbn. rewrite !map_app.
              rewrite removelast_app by congruence.
              rewrite !removelast_cons. 3: congruence.
              2: { intros H; symmetry in H; now apply app_cons_not_nil in H. }
              rewrite removelast_app by congruence. cbn. rewrite !map_rev.
              simpl_list. cbn. rewrite <- !app_assoc. cbn. rewrite !map_app. cbn. rewrite !map_rev.
              repeat first [ progress cbn | rewrite rev_app_distr | rewrite map_app | rewrite <- app_assoc | rewrite rev_involutive | rewrite map_map ].
              f_equal.
            + intros ? [ (?&<-&?) % in_map_iff | [<- | ] ] % in_app_iff; cbn; auto.
          - specialize (HCons (tps1 ++ [midtape ls m rs]) tps2' tp'). spec_assert HCons as [HCons ->]; auto.
            rewrite app_comm_cons' with (a := inr (sigList_X (RightBlank false))).
            rewrite MoveToSymbol_correct_midtape; cbn; auto.
            + cbn in *. TMSimp. rewrite map_id; cbv [id]. hnf. f_equal.
              rewrite encode_list_app. cbn. rewrite !map_app.
              * rewrite removelast_app by congruence.
                rewrite !removelast_cons. 3: congruence.
                2: { intros H; symmetry in H; now apply app_cons_not_nil in H. }
                rewrite removelast_app by congruence. cbn. rewrite !map_rev.
                simpl_list. cbn. rewrite <- !app_assoc. cbn. rewrite !map_app. cbn. rewrite !map_rev.
                repeat first [ progress cbn | rewrite rev_app_distr | rewrite map_app | rewrite <- app_assoc | rewrite rev_involutive | rewrite map_map ].
                f_equal.
              * now simpl_list.
            + intros ? [ (?&<-&?) % in_map_iff | [<- | ] ] % in_app_iff; cbn; auto.
        }
      }
    Qed.

    Definition GoToNext_steps' (t : tape sig) :=
      match t with
      | niltape _ => 8
      | leftof r rs => 16 + 4 * length rs
      | rightof r rs => 8
      | midtape ls m rs => 16 + 4 * length rs
      end.

    Definition GoToNext_steps (tp : tape sig) :=
        GoToNext_steps' tp + 3.

    Definition GoToNext_T : tRel sigSim 1 :=
      fun tin k => exists tps1 tps2 tp, atCons_current tin[@Fin0] tps1 tps2 tp /\ GoToNext_steps tp <= k.

    Lemma GoToNext_Terminates : projT1 GoToNext ↓ GoToNext_T.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold GoToNext. TM_Correct. eapply RealiseIn_TerminatesIn. apply IsCons_Sem. }
      { intros tin k (tps1&tps2&tp&HCons&Hk). hnf in HCons. unfold GoToNext_steps in Hk.
        exists (GoToNext_steps' tp), 2. repeat split. 2: lia. 2: intros _ _ _; reflexivity.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; hnf in HCons; TMSimp.
        { (* [tp = niltape] *)
          destruct tps2 as [ | tp' tps2']; cbn in *.
          - do 2 (rewrite MoveToSymbol_steps_equation; cbn). reflexivity.
          - do 2 (rewrite MoveToSymbol_steps_equation; cbn). reflexivity.
        }
        { (* [tp = leftof r rs] *)
          destruct tps2 as [ | tp' tps2']; cbn in *.
          - rewrite app_comm_cons' with (a := inr (sigList_X (RightBlank false))).
            rewrite app_comm_cons with (a := inr (sigList_X (UnmarkedSymbol r))).
            rewrite MoveToSymbol_steps_midtape; cbn; auto.
            simpl_list. cbn. lia.
          - rewrite app_comm_cons' with (a := inr (sigList_X (RightBlank false))).
            rewrite app_comm_cons with (a := inr (sigList_X (UnmarkedSymbol r))).
            rewrite MoveToSymbol_steps_midtape; cbn; auto.
            simpl_list. cbn. lia.
        }
        { (* [rightof l ls] *)
          destruct tps2 as [ | tp' tps2']; cbn in *.
          - do 2 (rewrite MoveToSymbol_steps_equation; cbn). reflexivity.
          - do 2 (rewrite MoveToSymbol_steps_equation; cbn). reflexivity.
        }
        { (* [midtape ls m rs *)
          destruct tps2 as [ | tp' tps2']; cbn in *.
          - rewrite app_comm_cons' with (a := inr (sigList_X (RightBlank false))).
            rewrite MoveToSymbol_steps_midtape; cbn; auto.
            simpl_list. cbn. lia.
          - rewrite app_comm_cons' with (a := inr (sigList_X (RightBlank false))).
            rewrite MoveToSymbol_steps_midtape; cbn; auto.
            simpl_list. cbn. lia.
        }
      }
    Qed.

  End GoToNext.


  (* Read the current symbols *)
  Section ReadCurrentSymbols.

    Local Arguments insertKnownSymbol : simpl never.
    (* Local Arguments insertKnownSymbols : simpl never. *)

    Definition ReadCurrent : pTM sigSim (option sig) 1 :=
      Switch ReadChar
             (fun (s : option sigSim) =>
                match s with
                | Some (inr (sigList_X (MarkedSymbol s))) => Return Nop (Some s)
                | _ => Return Nop None
                end).

    Definition ReadCurrent_Rel : pRel sigSim (option sig) 1 :=
      fun tin '(yout, tout) =>
        forall tps1 tps2 tp,
          atCons_current tin[@Fin0] tps1 tps2 tp ->
          atCons_current tout[@Fin0] tps1 tps2 tp /\
          yout = current tp.

    Definition ReadCurrent_steps := 2.

    Lemma ReadCurrent_Sem : ReadCurrent ⊨c(ReadCurrent_steps) ReadCurrent_Rel.
    Proof.
      unfold ReadCurrent_steps. eapply RealiseIn_monotone.
      { unfold ReadCurrent. TM_Correct. }
      { Unshelve. 4,5: reflexivity. all: reflexivity. }
      { intros tin (yout, tout) H. intros tps1 tps2 tp HCons.
        unfold atCons_current in *. TMSimp.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; hnf in HCons; TMSimp.
        all: (split; hnf; auto).
      }
    Qed.
        

    Definition ReadCurrentSymbols_Step_Rel (st : Vector.t (option sig) n * Fin.t n) :
      pRel sigSim (Vector.t (option sig) n * Fin.t n + Vector.t (option sig) n) 1 :=
      fun tin '(yout, tout) =>
        (forall tps1 tps2 tp ,
            (length tps1 =? fin_to_nat (snd st)) = true ->
            (length tps1 + (1 + length tps2) =? n) = true ->
            atCons tin[@Fin0] tps1 tps2 tp ->
            knowsFirstSymbols (fst st) tps1 ->
            match tps2 with
            | nil =>
              atNil tout[@Fin0] (tps1 ++ [tp]) /\
              yout = inr (insertKnownSymbol (fst st) (snd st) (current tp))
            | tp' :: tps2' =>
              atCons tout[@Fin0] (tps1 ++ [tp]) tps2' tp' /\
              match finSucc_opt (snd st) with
              | Some i' =>
                yout = inl (insertKnownSymbol (fst st) (snd st) (current tp), i')
              | None => False
              end
            end) /\
        (forall tps,
            atNil tin[@Fin0] tps ->
            atNil tout[@Fin0] tps /\
            yout = inr (fst st)).

    Definition ReadCurrentSymbols_Step : forall (st : Vector.t (option sig) n * Fin.t n),
        pTM sigSim (Vector.t (option sig) n * Fin.t n + Vector.t (option sig) n) 1 :=
      fun '(readSymbols, i) =>
        If IsCons
           (GoToCurrent;;
            Switch (ReadCurrent)
                   (fun (c : option sig) =>
                      Return (GoToNext)
                             (match finSucc_opt i with
                              | None =>
                                inr (insertKnownSymbol readSymbols i c)
                              | Some i' =>
                                inl (insertKnownSymbol readSymbols i c, i')
                              end)))
           (Return Nop (inr readSymbols)).
      
    Lemma ReadCurrentSymbols_Step_Realise : forall st, ReadCurrentSymbols_Step st ⊨ ReadCurrentSymbols_Step_Rel st.
    Proof.
      intros (readSymbols,i). eapply Realise_monotone.
      { unfold ReadCurrentSymbols_Step. TM_Correct_step; [ | TM_Correct_step | TM_Correct].
        - eapply RealiseIn_Realise. apply IsCons_Sem.
        - apply GoToCurrent_Realise.
        - apply Switch_Realise.
          + eapply RealiseIn_Realise. apply ReadCurrent_Sem.
          + intros c. apply Return_Realise. apply GoToNext_Realise. }
      {
        intros tin (yout, tout). TMSimp. split.
        {
          intros tps1 tps2 tp HL1 HL2 HCons HKnown.
          destruct H; TMSimp.
          { (* [cons] case *)
            rename H into HIsCons_cons, H0 into HGotoCurrent, H1 into IsCons_nil, H2 into HReadCurrent, H4 into HGoToNext.
            specialize HIsCons_cons with (1 := HCons) as (HIsCons_cons&_).
            specialize HGotoCurrent with (1 := HIsCons_cons) as (HGotoCurrent&->).
            specialize HReadCurrent with (1 := HGotoCurrent) as (HReadCurrent&->).
            specialize HGoToNext with (1 := HReadCurrent).
            destruct ymid1, tps2 as [ | tp' tps2']; auto.
            { (* tps = tp' :: tps' *) split; auto.
              destruct (finSucc_opt i) as [i'| ] eqn:Ei.
              - reflexivity.
              - exfalso. apply finSucc_opt_None' in Ei. apply Nat.eqb_eq in HL1. apply Nat.eqb_eq in HL2. cbn in *. lia.
            }
            { (* tps = nil *) split; auto.
              enough (finSucc_opt i = None) as -> by reflexivity.
              apply finSucc_opt_None.
              apply Nat.eqb_eq in HL1. apply Nat.eqb_eq in HL2. cbn in *. lia.
            }
          }
          { (* wrong [nil] case *) specialize H with (1 := HCons) as (_&H); congruence. }
        }
        { (* [nil] case *)
          intros tps HNil.
          destruct H; TMSimp.
          { (* wrong [cons] case *) specialize H1 with (1 := HNil) as (_&H1); congruence. }
          { now specialize H2 with (1 := HNil) as (H0&_). }
        }
      }
    Qed.


    Definition ReadCurrentSymbols_Step_steps_cons tp :=
      3 + IsCons_steps + GoToCurrent_steps tp + ReadCurrent_steps + GoToNext_steps tp.

    Definition ReadCurrentSymbols_Step_steps_nil := 1 + IsCons_steps.

    Definition ReadCurrentSymbols_Step_T : tRel sigSim 1 :=
      fun tin k =>
        (exists tps1 tps2 tp, atCons tin[@Fin0] tps1 tps2 tp /\ ReadCurrentSymbols_Step_steps_cons tp <= k) \/
        (exists tps, atNil tin[@Fin0] tps /\ ReadCurrentSymbols_Step_steps_nil <= k).

    Lemma ReadCurrentSymbols_Step_Terminates st : projT1 (ReadCurrentSymbols_Step st) ↓ ReadCurrentSymbols_Step_T.
    Proof.
      destruct st as [readSymbols i]. eapply TerminatesIn_monotone.
      { unfold ReadCurrentSymbols_Step. TM_Correct_step.
        { eapply RealiseIn_Realise. apply IsCons_Sem. }
        { eapply RealiseIn_TerminatesIn. apply IsCons_Sem. }
        { TM_Correct_step. apply GoToCurrent_Realise. apply GoToCurrent_Terminates.
          apply Switch_TerminatesIn.
          - eapply RealiseIn_Realise. apply ReadCurrent_Sem.
          - eapply RealiseIn_TerminatesIn. apply ReadCurrent_Sem.
          - intros st. apply Return_Terminates. apply GoToNext_Terminates. }
        { TM_Correct. }
      }
      {
        intros tin k. intros [ (tps1&tps2&tp&HCons&Hk) | (tps&HNil&Hk) ].
        { (* cons case *) unfold ReadCurrentSymbols_Step_steps_cons in Hk.
          exists (IsCons_steps), (2 + GoToCurrent_steps tp + ReadCurrent_steps + GoToNext_steps tp). repeat split; try lia.
          intros tmid ymid (HIsCons_cons&HIsCons_nil). specialize HIsCons_cons with (1 := HCons) as (HIsCons&->).
          exists (GoToCurrent_steps tp), (1 + ReadCurrent_steps + GoToNext_steps tp). repeat split; try lia. hnf; eauto.
          intros tmid0 ymid0 HGoToCurrent. cbn in HGoToCurrent. specialize HGoToCurrent with (1 := HIsCons) as (HGoToCurrent&->).
          exists (ReadCurrent_steps), (GoToNext_steps tp). repeat split; try lia.
          intros tmid1 ymid1 HReadCurrent. cbn in HReadCurrent. specialize HReadCurrent with (1 := HGoToCurrent) as (HReadCurrent&->). hnf. eauto.
        }
        { (* nil case *)  unfold ReadCurrentSymbols_Step_steps_nil in Hk.
          exists (IsCons_steps), 0. repeat split; try lia.
          intros tmid ymid (HIsCons_cons&HIsCons_nil). specialize HIsCons_nil with (1 := HNil) as (HIsNil&->). reflexivity.
        }
      }
    Qed.
          


    Definition ReadCurrentSymbols_Loop := StateWhile ReadCurrentSymbols_Step.

    Definition ReadCurrentSymbols_Loop_Rel (st : Vector.t (option sig) n * Fin.t n) :
      pRel sigSim (Vector.t (option sig) n) 1 :=
      fun tin '(yout, tout) =>
        (forall tps1 tp tps2,
            (length tps1 =? fin_to_nat (snd st)) = true ->
            (length tps1 + (1 + length tps2) =? n) = true ->
            atCons tin[@Fin0] tps1 tps2 tp ->
            knowsFirstSymbols (fst st) tps1 ->
            atNil tout[@Fin0] (tps1 ++ tp :: tps2) /\
            yout = insertKnownSymbols (fst st) (snd st) (current tp :: map (@current _) tps2)) /\
        (forall tps,
            (length tps =? n) = true ->
            atNil tin[@Fin0] tps ->
            knowsFirstSymbols (fst st) tps ->
            atNil tout[@Fin0] tps /\
            yout = (fst st)).

    Lemma ReadCurrentSymbols_Loop_Realise st : ReadCurrentSymbols_Loop st ⊨ ReadCurrentSymbols_Loop_Rel st.
    Proof.
      eapply Realise_monotone.
      { unfold ReadCurrentSymbols_Loop. TM_Correct. apply ReadCurrentSymbols_Step_Realise. }
      { revert st. apply StateWhileInduction; intros; rename l into st.
        {
          destruct st as [ readSymbols i]; cbn in *.
          destruct HLastStep as [HLastStepCons HLastStepNil].
          cbn. split; [intros tps1 tp tps2 HL1 HL2 HCons HRead | intros tps HL HNil HRead]; TMSimp.
          {
            specialize HLastStepCons with (1 := HL1) (2 := HL2) (3 := HCons) (4 := HRead).
            destruct tps2 as [ | tp' tps2']; cbn in *.
            - destruct HLastStepCons as [HLastStepCons HLastStepCons']; inv HLastStepCons'.
              split; auto.
              (*
              apply Nat.eqb_eq in HL1; apply Nat.eqb_eq in HL2. *)
              destruct (finSucc_opt i) as [i'| ]; auto.
            - destruct HLastStepCons as [ HLastStepCons HLastStepCons'].
              destruct (finSucc_opt i) as [i' | ]; auto. congruence.
          }
          { specialize HLastStepNil with (1 := HNil). destruct HLastStepNil as [H1 H2]. inv H2. split; auto. }
        }
        {
          destruct st as [ readSymbols i]; cbn in *.
          destruct HStar as [HStar_cons HStar_nil]. destruct HLastStep as [HLastStep_cons HLastStep_nil]. cbn in *.
          cbn. split; [intros tps1 tp tps2 HL1 HL2 HCons HRead | intros tps HL HNil HRead].
          {
            specialize HStar_cons with (1 := HL1) (2 := HL2) (3 := HCons) (4 := HRead).
            destruct tps2 as [ | tp' tps2']; cbn in *.
            - destruct HStar_cons as [HStar1 HStar2]. inv HStar2.
            - destruct HStar_cons as [HStar1 HStar2].
              destruct (finSucc_opt i) as [i' | ] eqn:E; auto. inv HStar2.
              specialize HLastStep_cons with (3 := HStar1).
              apply Nat.eqb_eq in HL1. apply Nat.eqb_eq in HL2. 
              spec_assert HLastStep_cons.
              { simpl_list; cbn. apply Nat.eqb_eq. apply finSucc_opt_Some' in E. lia. }
              spec_assert HLastStep_cons.
              { simpl_list; cbn. apply Nat.eqb_eq. apply finSucc_opt_Some' in E. lia. }
              spec_assert HLastStep_cons as [HLastStep_cons ->].
              { cbn. apply insertKnownSymbol_correct; auto. }
              cbn in *. rewrite <- app_assoc in HLastStep_cons. split; auto.
          }
          { specialize HStar_nil with (1 := HNil) as [HStar1 HStar2]; inv HStar2. }
        }
      }
    Qed.


    Definition ReadCurrentSymbols_Loop_steps_nil := ReadCurrentSymbols_Step_steps_nil.

    Fixpoint ReadCurrentSymbols_Loop_steps_cons tps2 tp :=
      match tps2 with
      | nil => ReadCurrentSymbols_Step_steps_cons tp
      | tp' :: tps2' => 1 + ReadCurrentSymbols_Step_steps_cons tp + ReadCurrentSymbols_Loop_steps_cons tps2' tp'
      end.

    Definition ReadCurrentSymbols_Loop_T (st : Vector.t (option sig) n * Fin.t n) : tRel sigSim 1 :=
      fun tin k =>
        (exists tps1 tps2 tp,
            (length tps1 =? fin_to_nat (snd st)) = true /\
            (length tps1 + (1 + length tps2) =? n) = true /\
            knowsFirstSymbols (fst st) tps1 /\
            atCons tin[@Fin0] tps1 tps2 tp /\ ReadCurrentSymbols_Loop_steps_cons tps2 tp <= k) \/
        (exists tps, atNil tin[@Fin0] tps /\ ReadCurrentSymbols_Loop_steps_nil <= k).

    Lemma ReadCurrentSymbols_Loop_Terminates st : projT1 (ReadCurrentSymbols_Loop st) ↓ ReadCurrentSymbols_Loop_T st.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold ReadCurrentSymbols_Loop. TM_Correct.
        - apply ReadCurrentSymbols_Step_Realise.
        - apply ReadCurrentSymbols_Step_Terminates. }
      {
        revert st. apply StateWhileCoInduction. intros (readSymbols&i). intros. unfold ReadCurrentSymbols_Loop_T in *. unfold ReadCurrentSymbols_Step_T in *.
        destruct HT as [ (tps1&tps2&tp&HL1&HL2&HRead&HCons&Hk) | (tps&HNil&Hk)].
        { (* cons case *)
           eexists. repeat split. left. eauto.
           intros ymid tmid (HStep_cons&HStep_nil). clear HStep_nil. cbn in *. destruct ymid as [ (readSymbols'&i') | result ].
           - (* continue case *)
             specialize HStep_cons with (1 := HL1) (2 := HL2) (3 := HCons) (4 := HRead).
             destruct tps2 as [ | tp' tps2']; cbn in *.
             + TMSimp. congruence.
             + destruct HStep_cons as (HStep_cons1&HStep_cons2). destruct (finSucc_opt i) as [ i'' | ] eqn:Ei; inv HStep_cons2; rename i'' into i'.
               eexists. split. 2: apply Hk. left. exists (tps1 ++ [tp]), (tps2'), tp'. repeat split.
               * simpl_list. cbn. apply finSucc_opt_Some' in Ei. apply Nat.eqb_eq. apply Nat.eqb_eq in HL1. lia.
               * simpl_list. cbn. apply finSucc_opt_Some' in Ei. apply Nat.eqb_eq. apply Nat.eqb_eq in HL2. lia.
               * apply insertKnownSymbol_correct. now apply Nat.eqb_eq. assumption.
               * assumption.
               * reflexivity.
           - (* break case *)
             specialize HStep_cons with (1 := HL1) (2 := HL2) (3 := HCons) (4 := HRead).
             destruct tps2 as [ | tp' tps2']; cbn in *.
             + lia.
             + lia.
        }
        { (* nil case *)
          eexists. repeat split. right. eauto.
          intros ymid tmid (HStep_cons&HStep_nil). clear HStep_cons. cbn in *. destruct ymid as [ (readSymbols'&i') | result ].
          - (* continue case *) specialize HStep_nil with (1 := HNil) as (?&?). congruence.
          - (* break case *) reflexivity.
        }
      }
    Qed.


    Definition ReadCurrentSymbols :=
      match (finMin_opt n) with
      | None => Return (Move Rmove) (Vector.const None n) (* Nothing to do, just move from the start to the nil symbol *)
      | Some min =>
        Move Rmove;; ReadCurrentSymbols_Loop (Vector.const None n, min)
      end.
    
    Definition ReadCurrentSymbols_Rel : pRel sigSim (Vector.t (option sig) n) 1 :=
      fun tin '(yout, tout) =>
        forall T,
          tin[@Fin0] ≃ T ->
          atNil tout[@Fin0] (vector_to_list T) /\
          yout = current_chars T.

    Lemma ReadCurrentSymbols_Realise : ReadCurrentSymbols ⊨ ReadCurrentSymbols_Rel.
    Proof.
      clear pM F. unfold ReadCurrentSymbols.
      destruct (finMin_opt n) as [min| ] eqn:E; swap 1 2.
      {
        eapply Realise_monotone.
        { TM_Correct. }
        { intros tin (yout, tout) H. intros T HEncT. unfold contains_tapes in *. TMSimp.
          clear_except E. apply finMin_opt_None in E as ->. destruct_tapes. cbn.
          split; cbn; auto. hnf. reflexivity.
        }
      }
      {
        eapply Realise_monotone.
        { TM_Correct. apply ReadCurrentSymbols_Loop_Realise. }
        { intros tin (yout, tout) H. intros T HEncT. unfold contains_tapes in *. TMSimp.
          rename H0 into HLoop_cons, H1 into HLoop_nil. clear HLoop_nil.
          pose proof finMin_opt_Some E as (n'&E'). pose (T' := Vector.cast T E').
          pose proof finMin_opt_Some_val E as E_val.
          specialize (HLoop_cons nil (Vector.hd T') (vector_to_list (Vector.tl T'))). cbn in *.
          rewrite E_val in HLoop_cons. subst. specialize HLoop_cons with (1 := eq_refl). spec_assert HLoop_cons.
          { rewrite vector_to_list_length. apply Nat.eqb_eq. reflexivity. } spec_assert HLoop_cons.
          { hnf. cbn. clear_all. destruct_tapes. cbn. f_equal. simpl_list. now rewrite vector_cast_refl. }
          spec_assert HLoop_cons as [HLoop_cons1 ->] by (cbn; tauto).
          rewrite vector_to_list_eta in HLoop_cons1. subst T'. rewrite vector_cast_refl in *. split; auto. 
          destruct (finSucc_opt min) as [minSucc | ] eqn:E2.
          - pose proof finSucc_opt_Some' E2 as E2_val. rewrite E_val in E2_val.
            now apply insertKnownSymbols_correct_cons.
          - apply finSucc_opt_None' in E2.
            apply Nat.succ_inj in E2. assert (n' = 0) as -> by lia. cbn.
            compute [insertKnownSymbol]. destruct_fin min. cbn.
            destruct_tapes. cbn. unfold current_chars. cbn. reflexivity.
        }
      }
    Qed.

    Definition ReadCurrentSymbols_steps (n : nat) (T : tapes sig n) :=
      match T with
      | [| |] => ReadCurrentSymbols_Loop_steps_nil
      | tp ::: T' => 2 + ReadCurrentSymbols_Loop_steps_cons (vector_to_list T') tp
      end.

    Definition ReadCurrentSymbols_T : tRel sigSim 1 :=
      fun tin k => exists T, tin[@Fin0] ≃ T /\ ReadCurrentSymbols_steps T <= k.

    Lemma ReadCurrentSymbols_Terminates : projT1 ReadCurrentSymbols ↓ ReadCurrentSymbols_T.
    Proof.
      unfold ReadCurrentSymbols.
      destruct (finMin_opt n) as [min| ] eqn:E.
      { eapply TerminatesIn_monotone.
        { TM_Correct. eapply ReadCurrentSymbols_Loop_Terminates. }
        {
          intros tin k (T&HEncT&Hk).
          pose proof finMin_opt_Some E as (n'&E'). pose proof finMin_opt_Some_val E as E_val.
          pose (T' := Vector.cast T E').
          exists 1, (ReadCurrentSymbols_Loop_steps_cons (vector_to_list (Vector.tl T')) (Vector.hd T')). repeat split; try lia.
          { rewrite <- Hk. clear_all. subst n T'. rewrite !vector_cast_refl. destruct_tapes. cbn. reflexivity. }
          {
            intros tmid [] HMove. cbn in HMove. hnf. left. exists (nil), (vector_to_list (Vector.tl T')), (Vector.hd T'). cbn. rewrite E_val. cbn. repeat split; auto.
            - rewrite vector_to_list_length. apply Nat.eqb_eq. lia.
            - apply knowsFirstSymbols_nil.
            - rewrite HMove. hnf in HEncT. cbn in *. rewrite HEncT. clear_all. subst n T'. cbn. rewrite !vector_cast_refl.
              destruct_tapes. cbn. hnf. f_equal. now rewrite !map_app, !List.map_map, <- !app_assoc.
          }
        }
      }
      { eapply TerminatesIn_monotone.
        { TM_Correct. }
        {
          intros tin k (T&HEnc&Hk). rewrite <- Hk. apply finMin_opt_None in E. clear_except E. subst. destruct_tapes. cbn. unfold ReadCurrentSymbols_Loop_steps_nil, ReadCurrentSymbols_Step_steps_nil. lia.
        }
      }
    Qed.
      
  End ReadCurrentSymbols.


  (* Move from the nil symbol back to the start symbol *)
  Section MoveToStart.

    Definition MoveToStart_Rel : pRel sigSim unit 1 :=
      ignoreParam
        (fun tin tout =>
           forall tps, atNil tin[@Fin0] tps ->
                  atStart tout[@Fin0] tps).

    Definition isStart : sigSim -> bool :=
      fun s => match s with
            | inl START => true
            | _ => false
            end.

    Definition MoveToStart : pTM sigSim unit 1 :=
      MoveToSymbol_L isStart id.


    Lemma MoveToStart_Realise : MoveToStart ⊨ MoveToStart_Rel.
    Proof.
      eapply Realise_monotone.
      { unfold MoveToStart. TM_Correct. }
      {
        intros tin (yout, tout) H. intros tps HNil. unfold atNil, atStart in *. TMSimp. clear_all.
        rewrite MoveToSymbol_L_correct_midtape; cbn; auto.
        - rewrite !map_id; cbv [id]. rewrite map_rev, rev_involutive.
          f_equal.
          change [inr (@sigList_nil (sigTape sig)); inl STOP]
            with (List.map inr [ @sigList_nil (sigTape sig)] ++ [inl STOP]).
          rewrite app_assoc, <- map_app. f_equal. f_equal.
          apply encode_list_remove.
        - intros ? (?&<-&?) % in_map_iff. cbn. reflexivity.
      }
    Qed.


    (*
    Definition tape_size (tp : tape sig) : nat :=
      match tp with
      | niltape _ => 1
      | rightof l ls => 3 + length ls
      | leftof r rs => 3 + length rs
      | midtape ls m rs => 3 + length ls + length rs
      end.

    Fixpoint tapes_size (tps : list (tape sig)) : nat :=
      match tps with
      | nil => 1
      | tp :: tps' => 1 + tape_size tp + tapes_size tps'
      end.

    Lemma tape_size_length (tp : tape sig) :
      tape_size tp = length (encode_tape tp).
    Proof. destruct tp eqn:E; cbn; simpl_list; cbn; auto. all: try lia. simpl_list. cbn. lia. Qed.

    Lemma tapes_size_length (tps : list (tape sig)) :
      tapes_size tps = length (encode_list _ tps).
    Proof.
      induction tps as [ | tp tsp].
      - cbn. reflexivity.
      - cbn.  simpl_list. rewrite <- IHtsp. cbn. rewrite <- tape_size_length. lia.
    Qed.
    *)

    Definition MoveToStart_steps (tps : list (tape sig)) :=
      8 + 4 * length (encode_list _ tps).
    
    Definition MoveToStart_T : tRel sigSim 1 :=
      fun tin k => exists tps, atNil tin[@Fin0] tps /\ MoveToStart_steps tps <= k.

    (* TODO: somewhere *)
    Lemma removelast_length (X : Type) (xs : list X) :
      length (removelast xs) = length xs - 1.
    Proof.
      induction xs as [ | x xs IH].
      - cbn. reflexivity.
      - cbn. destruct xs as [ | x' xs]; cbn in *.
        + reflexivity.
        + f_equal. rewrite IH. lia.
    Qed.

    Lemma MoveToStart_Terminates : projT1 MoveToStart ↓ MoveToStart_T.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold MoveToStart. TM_Correct. }
      {
        intros tin k (tps&HNil&Hk). hnf in HNil. TMSimp. rewrite MoveToSymbol_L_steps_midtape; cbn; auto. simpl_list. cbn.
        rewrite <- Hk. rewrite removelast_length. unfold MoveToStart_steps. lia.
      }
    Qed.

    Lemma atStart_contains (t : tape sigSim) (tps : list (tape sig)) (T : tapes sig n) :
      length tps = n ->
      atStart t tps ->
      vector_to_list T = tps ->
      t ≃ T.
    Proof.
      clear pM F.
      intros HL HStart HToList. unfold contains_tapes, atStart in *. subst.
      f_equal. f_equal. f_equal. unfold encode_tapes. f_equal. auto.
    Qed.

  End MoveToStart.


  Section DoActions.

    Variable (acts : Vector.t (option sig * move) n).

    (* Abuse [UNKNOWN] as a special marker, to return to the place where we inserted the symbol with shifting *)
    Definition isReturnMarker (s : sigSim) : bool :=
      match s with
      | inl UNKNOWN => true
      | _ => false
      end.

    (* The more complicated part is writing, because we may have to alocate more memory by shifting *)

    Definition DoWrite_Rel (d : option move) (s : sig) : pRel sigSim unit 1 :=
      ignoreParam
        (fun tin tout =>
           forall tps1 tps2 tp,
             tape_dir tp = d ->
             atCons_current tin[@Fin0] tps1 tps2 tp ->
             atCons_current tout[@Fin0] tps1 tps2 (tape_write tp (Some s))).

    Definition DoWrite (d : option move) (s : sig) : pTM sigSim unit 1 :=
      match d with
      | Some Lmove => (* [leftof] ~> shift left and change boundary symbol to [LeftBlank false] *)
        Shift_L (fun _ => false) (inl UNKNOWN);;
        MoveToSymbol isReturnMarker id;;
        WriteMove (inr (sigList_X (MarkedSymbol s))) Lmove;;
        WriteMove (inr (sigList_X (LeftBlank false))) Rmove
      | Some Rmove => (* [rightof] ~> shift right and change boundary symbol to [RightBlank false] *)
        Shift (fun _ => false) (inl UNKNOWN);;
        MoveToSymbol_L isReturnMarker id;;
        WriteMove (inr (sigList_X (MarkedSymbol s))) Rmove;;
        WriteMove (inr (sigList_X (RightBlank false))) Lmove
      | Some Nmove => (* [midtape] ~> just write the symbol *)
        Write (inr (sigList_X (MarkedSymbol s)))
      | None => (* [midtape] ~> we need to shift left and right and insert [RightBlank false] and [LeftBlank false] *)
        Shift (fun _ => false) (inl UNKNOWN);;
        MoveToSymbol_L isReturnMarker id;;
        Shift_L (fun _ => false) (inr (sigList_X (MarkedSymbol s)));;
        MoveToSymbol isReturnMarker id;;
        WriteMove (inr (sigList_X (LeftBlank false))) Rmove;;
        Move Rmove;;
        WriteMove (inr (sigList_X (RightBlank false))) Lmove
      end.

    Lemma DoWrite_Realise (d : option move) (s : sig) : DoWrite d s ⊨ DoWrite_Rel d s.
    Proof.
      unfold DoWrite. destruct d as [ [ | | ] | ].
      { (* Some Lmove (leftof) *) eapply Realise_monotone. TM_Correct.
        intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons. unfold atCons_current in *. TMSimp.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp. simpl_tape.
        unfold atCons_current_leftof in HCons. TMSimp.
        rewrite app_comm_cons. rewrite Shift_L_fun_correct_midtape; auto.
        rewrite app_comm_cons'. rewrite MoveToSymbol_correct_midtape; cbn; auto.
        - hnf. cbn. f_equal. f_equal. rewrite map_id, rev_app_distr; cbn; cbv [id].
          rewrite rev_app_distr. cbn. rewrite rev_involutive. reflexivity.
        - rewrite map_rev, rev_involutive.
          intros ? [ [ (?&<-&?) % in_map_iff | [ <- | ] ] % in_app_iff | [ <- | ] ] % in_app_iff; cbn; auto.
      }
      { (* Some Rmove (rightof) *) eapply Realise_monotone. TM_Correct.
        intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons. unfold atCons_current in *. TMSimp.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp. simpl_tape.
        unfold atCons_current_rightof in HCons. TMSimp.
        rewrite Shift_fun_correct_midtape; auto.
        rewrite app_comm_cons'. rewrite MoveToSymbol_L_correct_midtape; cbn; auto.
        - hnf. cbn. f_equal. f_equal. rewrite map_id, rev_app_distr; cbn. now rewrite rev_involutive.
        - intros ? [ (?&<-&?) % in_rev % in_map_iff | [ <- | ] ] % in_app_iff; cbn; auto.
      }
      { (* Some Nmove (midtape) *) eapply Realise_monotone. TM_Correct.
        intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons. unfold atCons_current in *. TMSimp.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
        unfold atCons_current_midtape in HCons. TMSimp.
        hnf. cbn. reflexivity.
      }
      { (* None (niltape) *) eapply Realise_monotone. TM_Correct.
        intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons. unfold atCons_current in *. TMSimp.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
        unfold atCons_current_niltape in HCons. TMSimp.
        simpl_tape. rewrite Shift_fun_correct_midtape; auto. cbn.
        rewrite app_comm_cons'. rewrite MoveToSymbol_L_correct_midtape; cbn; auto.
        + rewrite app_comm_cons. rewrite Shift_L_fun_correct_midtape; auto; cbn.
          rewrite map_rev, rev_involutive, !map_id. rewrite MoveToSymbol_correct_midtape; cbn; auto.
          * simpl_tape. rewrite !map_id. cbv [id]. cbn. rewrite !rev_app_distr. cbn.
            hnf. cbn. rewrite <- !map_rev. rewrite !rev_involutive. reflexivity.
          * intros ? [ (?&<-&?) % in_map_iff | [ <- | ] ] % in_app_iff; cbn; auto.
        + intros ? [ (?&<-&?) % in_rev % in_map_iff | [ <- | ] ] % in_app_iff; cbn; auto.
      }
    Qed.


    Definition DoWrite_steps (d : option move) (tps1 tps2 : list (tape sig)) :=
      match d with
      | Some Lmove => 37 + 8 * length (encode_list _ tps1)
      | Some Rmove => 37 + 8 * length (encode_list _ tps2)
      | Some Nmove => 1
      | None => 73 + 8 * length (encode_list _ tps1) + 8 * length (encode_list _ tps2)
      end.

    Definition DoWrite_T (d : option move) : tRel sigSim 1 :=
      fun tin k => exists tps1 tps2 tp, tape_dir tp = d /\ atCons_current tin[@Fin0] tps1 tps2 tp /\ DoWrite_steps d tps1 tps2 <= k.

    Lemma DoWrite_Terminates (d : option move) (s : sig) : projT1 (DoWrite d s) ↓ DoWrite_T d.
    Proof.
      unfold DoWrite. destruct d as [ [ | | ] | ].
      { (* [d = Some Lmove] (leftof) *) eapply TerminatesIn_monotone. TM_Correct.
        intros tin k (tps1&tps2&tp&HDir&HCons&Hk). cbn in *.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir.
        unfold atCons_current_leftof in HCons. TMSimp.
        exists (16 + 4 * length (encode_list _ tps1)), (20 + 4 * length (encode_list _ tps1)). repeat split.
        { rewrite Shift_steps_local. simpl_list; cbn. rewrite removelast_length. lia. }
        { lia. }
        intros tmid [] ->. exists (16 + 4 * length (encode_list _ tps1)), 3. repeat split.
        { rewrite app_comm_cons. rewrite Shift_L_fun_correct_midtape; auto. rewrite app_comm_cons'. rewrite MoveToSymbol_steps_midtape; cbn; auto.
          simpl_list. rewrite removelast_length. cbn. lia. }
        { lia. }
        intros ? [] ?. exists 1, 1. repeat split. reflexivity. reflexivity. intros _ _ _. reflexivity.
      }
      { (* [d = Some Rmove] (rightof) *) eapply TerminatesIn_monotone. TM_Correct.
        intros tin k (tps1&tps2&tp&HDir&HCons&Hk). cbn in *.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir.
        unfold atCons_current_rightof in HCons. TMSimp.
        exists (16 + 4 * length (encode_list _ tps2)), (20 + 4 * length (encode_list _ tps2)). repeat split.
        { rewrite Shift_steps_local. simpl_list; cbn. lia. }
        { lia. }
        intros tmid [] ->. exists (16 + 4 * length (encode_list _ tps2)), 3. repeat split.
        { rewrite app_comm_cons. rewrite Shift_fun_correct_midtape; auto. rewrite app_comm_cons'. rewrite MoveToSymbol_L_steps_midtape; cbn; auto.
          simpl_list. cbn. lia. }
        { lia. }
        intros ? [] ?. exists 1, 1. repeat split. reflexivity. reflexivity. intros _ _ _. reflexivity.
      }
      { (* [d = Somme Nmove] (midtape) *) eapply TerminatesIn_monotone. TM_Correct.
        intros tin k (tps1&tps2&tp&HDir&HCons&Hk). cbn in *. assumption.
      }
      { (* [d = None] (niltapp) *) eapply TerminatesIn_monotone. TM_Correct.
        intros tin k (tps1&tps2&tp&HDir&HCons&Hk). cbn in *.
        destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir.
        unfold atCons_current_niltape in HCons. TMSimp.
        rewrite Shift_fun_correct_midtape; auto. cbn.
        exists (16 + 4 * length (encode_list _ tps2)), (56 + 8 * length (encode_list _ tps1) + 4 * length (encode_list _ tps2)). repeat split; try lia.
        { rewrite Shift_steps_local. simpl_list. cbn. lia. }
        intros tmid [] ->. exists (16 + 4 * length (encode_list _ tps2)), (39 + 8 * length (encode_list _ tps1)). repeat split; try lia.
        { rewrite app_comm_cons. rewrite app_comm_cons'. rewrite MoveToSymbol_L_steps_midtape; cbn; auto. simpl_list. cbn. lia. }
        intros tmid0 [] ->.
        rewrite app_comm_cons. rewrite app_comm_cons'. rewrite MoveToSymbol_L_correct_midtape; cbn; auto.
        2: { intros ? [ (?&<-&?) % in_rev % in_map_iff | [ <- | ] ] % in_app_iff; cbn; auto. }
        exists (16 + 4 * length (encode_list _ tps1)), (22 + 4 * length (encode_list _ tps1)). repeat split; try lia.
        { rewrite Shift_steps_local. simpl_list. cbn. rewrite removelast_length. lia. }
        intros tmid1 [] ->. exists (16 + 4 * length (encode_list _ tps1)), (5). repeat split; try lia.
        { rewrite app_comm_cons. rewrite Shift_L_fun_correct_midtape; auto. rewrite MoveToSymbol_steps_midtape; cbn; auto.
          simpl_list. rewrite removelast_length. cbn. lia. }
        (* constant time *)
        intros ? [] ?. exists 1, 3. repeat split. reflexivity. reflexivity. intros ? ? ?. exists 1, 1. repeat split. reflexivity. reflexivity. intros _ _ _. reflexivity.
      }
    Qed.


    Definition DoMove_Rel (d : option move) (m : move) : pRel sigSim unit 1 :=
      ignoreParam
        (fun tin tout =>
           forall tps1 tps2 tp,
             tape_dir tp = d ->
             atCons_current tin[@Fin0] tps1 tps2 tp ->
             atCons_current tout[@Fin0] tps1 tps2 (tape_move tp m)).


    Definition toggle_marked (s : sigTape sig) : sigTape sig :=
      match s with
      | UnmarkedSymbol s => MarkedSymbol s
      | MarkedSymbol s => UnmarkedSymbol s
      | LeftBlank b => LeftBlank (negb b)
      | RightBlank b => RightBlank (negb b)
      | NilBlank => NilBlank
      end.

    Definition ToggleMarked_Rel : pRel sigSim unit 1 :=
      ignoreParam (fun tin tout => forall ls m rs,
                       tin[@Fin0] = midtape ls (inr (sigList_X m)) rs ->
                       tout[@Fin0] = midtape ls (inr (sigList_X (toggle_marked m))) rs).

    Definition ToggleMarked : pTM sigSim unit 1 :=
      Switch ReadChar
             (fun (s : option sigSim) =>
                match s with
                | Some (inr (sigList_X m)) => Write (inr (sigList_X (toggle_marked m)))
                | _ => Nop
                end).

    Lemma ToggleMarked_Sem : ToggleMarked ⊨c(3) ToggleMarked_Rel.
    Proof.
      eapply RealiseIn_monotone.
      { unfold ToggleMarked. TM_Correct. }
      { Unshelve. 4, 11: reflexivity. all: lia. }
      { intros tin ([], tout) H. intros ls m rs Hmidtape. TMCrush; TMSolve 1. }
    Qed.

    (* this should take constant time *)
    Definition DoMove (d : option move) (m : move) : pTM sigSim unit 1 :=
      match d with
      | Some Lmove => match m with
                 | Nmove => Nop
                 | Lmove => Nop
                 | Rmove => ToggleMarked;; Move Rmove;; ToggleMarked
                 end
      | Some Rmove => match m with
                 | Nmove => Nop
                 | Rmove => Nop
                 | Lmove => ToggleMarked;; Move Lmove;; ToggleMarked
                 end
      | Some Nmove => match m with
                 | Nmove => Nop
                 | Rmove => ToggleMarked;; Move Rmove;; ToggleMarked
                 | Lmove => ToggleMarked;; Move Lmove;; ToggleMarked
                 end
      | None => Nop
      end.

    
    Definition DoMove_steps := 9.

    Lemma DoMove_Sem (d : option move) (m : move) : DoMove d m ⊨c(DoMove_steps) DoMove_Rel d m.
    Proof.
      unfold DoMove_steps. unfold DoMove. destruct d as [ [ | | ] | ].
      { (* [leftof] *)
        destruct m; cbn.
        { eapply RealiseIn_monotone. TM_Correct. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_leftof in *. TMSimp. f_equal. }
        { eapply RealiseIn_monotone. TM_Correct; apply ToggleMarked_Sem. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_leftof, atCons_current_midtape in *. TMSimp.
          specialize H with (1 := eq_refl); TMSimp; specialize H1 with (1 := eq_refl); TMSimp. f_equal. }
        { eapply RealiseIn_monotone. TM_Correct. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_leftof in *. TMSimp. f_equal. }
      }
      { (* [rightof] *)
        destruct m; cbn.
        { eapply RealiseIn_monotone. TM_Correct; apply ToggleMarked_Sem. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_rightof, atCons_current_midtape in *. TMSimp.
          specialize H with (1 := eq_refl); TMSimp; specialize H1 with (1 := eq_refl); TMSimp. f_equal. }
        { eapply RealiseIn_monotone. TM_Correct. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_rightof in *. TMSimp. f_equal. }
        { eapply RealiseIn_monotone. TM_Correct. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_rightof in *. TMSimp. f_equal. }
      }
      { (* midtape *)
        destruct m; cbn.
        { (* [Lmove] *)
          eapply RealiseIn_monotone. TM_Correct; apply ToggleMarked_Sem. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_midtape, atCons_current_midtape in *. TMSimp.
          specialize H with (1 := eq_refl); TMSimp.
          destruct ls as [ | l' ls']; cbn in *.
          { specialize H1 with (1 := eq_refl). TMSimp. hnf. f_equal. }
          { specialize H1 with (1 := eq_refl). TMSimp. hnf. f_equal. }
        }
        { (* [Rmove] *)
          eapply RealiseIn_monotone. TM_Correct; apply ToggleMarked_Sem. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_midtape in *. TMSimp.
          specialize H with (1 := eq_refl); TMSimp.
          destruct rs as [ | r' rs']; cbn in *.
          { specialize H1 with (1 := eq_refl). TMSimp. hnf. f_equal. }
          { specialize H1 with (1 := eq_refl). TMSimp. hnf. f_equal. }
        }
        { (* [Nmove] *)
          eapply RealiseIn_monotone. TM_Correct; apply ToggleMarked_Sem. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
          destruct tp as [ | r rs | l ls | ls m rs ]; cbn in *; inv HDir; TMSimp.
          unfold atCons_current_midtape in *. TMSimp. f_equal. }
      }
      { (* [niltape] *)
        eapply RealiseIn_monotone. TM_Correct; apply ToggleMarked_Sem. lia. intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons.
        destruct tp as [ | r rs | l ls | ls m' rs ]; cbn in *; inv HDir; TMSimp.
        now simpl_tape in *.
      }
    Qed.

    Arguments DoMove : simpl never.


    (* First write, then move *)
    Definition DoAction_Rel (d : option move) (a : option sig * move) : pRel sigSim unit 1 :=
      ignoreParam
        (fun tin tout =>
           forall (tps1 tps2 : list (tape sig)) (tp : tape sig),
             tape_dir tp = d ->
             atCons_current tin[@Fin0] tps1 tps2 tp ->
             atCons_current tout[@Fin0] tps1 tps2 (doAct tp a)).


    Definition DoAction (d : option move) (a : option sig * move) : pTM sigSim unit 1 :=
      match (fst a) with
      | Some s => DoWrite d s;; DoMove (Some Nmove) (snd a) (* after wrting, we have a [midtape] *)
      | None => DoMove d (snd a)
      end.

    Lemma DoAction_Realise (d : option move) (a : option sig * move) : DoAction d a ⊨ DoAction_Rel d a.
    Proof.
      unfold DoAction. destruct a as [[ w | ] m]; cbn.
      { (* Write [w] and move [m] *)
        eapply Realise_monotone. TM_Correct. apply DoWrite_Realise. eapply RealiseIn_Realise. apply DoMove_Sem.
        intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons. TMSimp.
        rename H into HWrite, H0 into HMove.
        specialize HWrite with (1 := eq_refl) (2 := HCons).
        specialize (HMove tps1 tps2 (midtape (left tp) w (right tp))). cbn in *. auto.
      }
      { (* Just move [m] *)
        eapply Realise_monotone. eapply RealiseIn_Realise. apply DoMove_Sem.
        intros tin ([], tout) H. intros tps1 tps2 tp HDir HCons. TMSimp.
        specialize H with (1 := eq_refl) (2 := HCons). auto.
      }
    Qed.


    Definition DoAction_steps (d : option move) (a : option sig * move) (tps1 tps2 : list (tape sig)) :=
      match (fst a) with
      | Some s => 1 + DoWrite_steps d tps1 tps2 + DoMove_steps
      | None => DoMove_steps
      end.

    Definition DoAction_T (d : option move) (a : option sig * move) : tRel sigSim 1 :=
      fun tin k => exists tps1 tps2 tp, tape_dir tp = d /\ atCons_current tin[@Fin0] tps1 tps2 tp /\ DoAction_steps d a tps1 tps2 <= k.

    Lemma DoAction_Terminates (d : option move) (a : option sig * move) : projT1 (DoAction d a) ↓ DoAction_T d a.
    Proof.
      unfold DoAction. destruct a as [ [ w | ] m]; cbn in *.
      { (* Write and Move *) eapply TerminatesIn_monotone.
        { TM_Correct.
          - apply DoWrite_Realise.
          - apply DoWrite_Terminates.
          - eapply RealiseIn_TerminatesIn. apply DoMove_Sem. }
        { intros tin k. intros (tps1&tps2&tp&HDir&HCons&Hk). cbn in *. exists (DoWrite_steps d tps1 tps2), DoMove_steps. repeat split; try lia.
          { hnf. do 3 eexists. repeat split; eauto. }
        }
      }
      { (* Only Move *) eapply TerminatesIn_monotone.
        { eapply RealiseIn_TerminatesIn. apply DoMove_Sem. }
        { intros tin k. intros (tps1&tps2&tp&HDir&HCons&Hk). cbn in *. assumption. }
      }
    Qed.
      


    Definition DoActions_Step_Rel (i : Fin.t n) : pRel sigSim (Fin.t n + unit) 1 :=
      fun tin '(yout, tout) =>
        (forall tps1 tps2 tp,
            (length tps1 =? fin_to_nat i) = true ->
            (length tps1 + (1 + length tps2) =? n) = true ->
            atCons tin[@Fin0] tps1 tps2 tp ->
            match tps2 with
            | tp' :: tps2' =>
              atCons tout[@Fin0] (tps1 ++ [doAct tp acts[@i]]) tps2' tp' /\
              match finSucc_opt i with
              | Some i' => yout = inl i'
              | None => False
              end
            | nil =>
              atNil tout[@Fin0] (tps1 ++ [doAct tp acts[@i]]) /\
              yout = inr tt
            end) /\
        (forall tps,
            atNil tin[@Fin0] tps ->
            atNil tout[@Fin0] tps /\
            yout = inr tt).

    Definition opt_to_sum_unit (X : Type) (x : option X) : X + unit :=
      match x with
      | Some x => inl x
      | None => inr tt
      end.

    Definition DoActions_Step (i : Fin.t n) : pTM sigSim (Fin.t n + unit) 1 :=
      If IsCons
         (Switch GoToCurrent
                 (fun (d : option move) =>
                    Return (DoAction d (acts[@i]);; GoToNext) (opt_to_sum_unit (finSucc_opt i))))
         (Return Nop (inr tt)).

    Lemma DoActions_Step_Realise (i : Fin.t n) : DoActions_Step i ⊨ DoActions_Step_Rel i.
    Proof.
      eapply Realise_monotone.
      { apply If_Realise.
        { eapply RealiseIn_Realise. apply IsCons_Sem. }
        { apply Switch_Realise.
          - apply GoToCurrent_Realise.
          - intros d. TM_Correct.
            + apply DoAction_Realise.
            + apply GoToNext_Realise. }
        { TM_Correct. }
      }
      {
        intros tin (yout, tout) H; split.
        { (* [cons] case *)
          intros tps1 tps2 tp HL1 HL2 HCons. TMSimp.
          destruct H; TMSimp; swap 1 2.
          { specialize H with (1 := HCons) as (_&?). congruence. }
          rename H into HIsCons, H0 into HGoToCurrent, H3 into HDoAct, H4 into HDoActs_Step.
          specialize HIsCons with (1 := HCons) as (HIsCons&_).
          specialize HGoToCurrent with (1 := HIsCons) as (HGoToCurrent1&->).
          apply Nat.eqb_eq in HL1; apply Nat.eqb_eq in HL2.
          specialize HDoAct with (1 := eq_refl) (2 := HGoToCurrent1).
          specialize HDoActs_Step with (1 := HDoAct).
          destruct tps2 as [ | tp' tps2']; (destruct ymid0; auto).
          - split; auto. cbn in *.
            unshelve epose proof @finSucc_opt_None n i _ as ->. lia. reflexivity.
          - split; auto. cbn in *.
            unshelve epose proof @finSucc_opt_Some n i _ as (i'&->). lia. reflexivity.
        }
        { (* [nil] case *)
          intros tps HNil.
          destruct H; TMSimp.
          { specialize H1 with (1 := HNil) as (_&?). congruence. }
          now specialize H2 with (1 := HNil) as (HIsNil&_).
        }
      }
    Qed.


    Definition DoActions_Step_steps_cons i tps1 tps2 tp :=
      3 + IsCons_steps + GoToCurrent_steps tp + DoAction_steps (tape_dir tp) (acts[@i]) tps1 tps2 + GoToNext_steps (doAct tp acts[@i]).

    Definition DoActions_Step_steps_nil := 1 + IsCons_steps.
      
    Definition DoActions_Step_T (i : Fin.t n) : tRel sigSim 1 :=
      fun tin k =>
        (exists tps1 tps2 tp,
            (length tps1 =? fin_to_nat i) = true /\
            (length tps1 + (1 + length tps2) =? n) = true /\
            atCons tin[@Fin0] tps1 tps2 tp /\
            DoActions_Step_steps_cons i tps1 tps2 tp <= k) \/
        (exists tps, atNil tin[@Fin0] tps /\ DoActions_Step_steps_nil <= k).

    Lemma DoActions_Step_Terminates (i : Fin.t n) : projT1 (DoActions_Step i) ↓ DoActions_Step_T i.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold DoActions_Step. TM_Correct_step.
        { eapply RealiseIn_Realise. apply IsCons_Sem. }
        { eapply RealiseIn_TerminatesIn. apply IsCons_Sem. }
        { apply Switch_TerminatesIn. apply GoToCurrent_Realise. apply GoToCurrent_Terminates. intros i'.
          TM_Correct. apply DoAction_Realise. apply DoAction_Terminates. apply GoToNext_Terminates. }
        { TM_Correct. }
      }
      {
        intros tin k [ (tps1&tps2&tp&HL1&HL2&HCons&Hk) | (tps&HNil&Hk) ].
        { (* cons case *) unfold DoActions_Step_steps_cons in Hk.
          exists (IsCons_steps), (2 + GoToCurrent_steps tp + DoAction_steps (tape_dir tp) (acts[@i]) tps1 tps2 + GoToNext_steps (doAct tp acts[@i])). repeat split; try lia.
          intros tmid ymid (HIsCons_cons&_). specialize HIsCons_cons with (1 := HCons) as (HIsCons&->).
          exists (GoToCurrent_steps tp), (1 + DoAction_steps (tape_dir tp) (acts[@i]) tps1 tps2 + GoToNext_steps (doAct tp acts[@i])). repeat split; try lia.
          { hnf. eauto. }
          intros tmid0 ymid0 HGoToCurrent. cbn in HGoToCurrent. specialize HGoToCurrent with (1 := HIsCons) as (HGoToCurrent&->).
          exists (DoAction_steps (tape_dir tp) (acts[@i]) tps1 tps2), (GoToNext_steps (doAct tp acts[@i])). repeat split; try lia.
          { hnf. eauto 6. }
          intros tmid1 ymid1 HDoAction. cbn in HDoAction. specialize HDoAction with (1 := eq_refl) (2 := HGoToCurrent).
          { hnf. eauto. }
        }
        { (* nil case *) unfold DoActions_Step_steps_nil in Hk.
          exists IsCons_steps, 0. repeat split; try lia.
          intros tmid ymid (_&HIsCons_nil). specialize HIsCons_nil with (1 := HNil) as (HIsNil&->). reflexivity.
        }
      }
    Qed.


    Definition DoActions_Loop : Fin.t n -> pTM sigSim unit 1 := StateWhile DoActions_Step.

    Definition DoActions_Loop_Rel (i : Fin.t n) : pRel sigSim unit 1 :=
      fun tin '(yout, tout) =>
        (forall tps1 tps2 tp,
            (length tps1 =? fin_to_nat i) = true ->
            (length tps1 + (1 + length tps2) =? n) = true ->
            atCons tin[@Fin0] (map_vect_list (@doAct sig) acts tps1) tps2 tp ->
            atNil tout[@Fin0] (map_vect_list (@doAct sig) acts (tps1 ++ tp :: tps2))
        ) /\
        (forall tps,
            atNil tin[@Fin0] tps ->
            atNil tout[@Fin0] tps).

    Lemma DoActions_Loop_Realise (i : Fin.t n) : DoActions_Loop i ⊨ DoActions_Loop_Rel i.
    Proof.
      eapply Realise_monotone.
      { unfold DoActions_Loop. TM_Correct.
        - apply DoActions_Step_Realise. }
      {
        revert i; apply StateWhileInduction; intros; rename l into i.
        { (* [cons] case *)
          split.
          {
            intros tps1 tps2 tp HL1 HL2 HCons. TMSimp. rename H into HCaseCons, H0 into HCaseNil.
            specialize HCaseCons with (3 := HCons).
            do 2 spec_assert HCaseCons by now rewrite map_vect_list_length.
            destruct tps2 as [ | tp' tps']; destruct HCaseCons as [HCaseCons1 HCaseCons2].
            - apply Nat.eqb_eq in HL1; apply Nat.eqb_eq in HL2; cbn in *.
              assert (S (fin_to_nat i) = n) by lia. clear HCaseCons2.
              replace (map_vect_list (doAct (sig:=eqType_X (type sig))) acts (tps1 ++ [tp])) with
                  (map_vect_list (doAct (sig:=eqType_X (type sig))) acts tps1 ++ [doAct tp acts[@i]]); auto.
              symmetry. apply map_vect_list_app. lia.
            - apply Nat.eqb_eq in HL1; apply Nat.eqb_eq in HL2; cbn in *.
              assert (S (fin_to_nat i) < n) by lia.
              apply finSucc_opt_Some in H as (i'&H). rewrite H in HCaseCons2. inv HCaseCons2.
          }
          { intros tps HNil. TMSimp. now specialize H0 with (1 := HNil). }
        }
        { (* [nil] case *)
          split.
          {
            intros tps1 tps2 tp HL1 HL2 HCons. TMSimp.
            rename H1 into HCaseCons1, H2 into HCaseNil1, H into HCaseCons2, H0 into HCaseNil2.
            specialize HCaseCons1 with (3 := HCons).
            do 2 spec_assert HCaseCons1 by now rewrite map_vect_list_length.
            destruct tps2 as [ | tp' tps2'].
            - destruct HCaseCons1 as [ _ ? ]. inv H.
            - destruct HCaseCons1 as [ HCaseCons1 ? ]. destruct (finSucc_opt i) as [ i' | ] eqn:E; auto. inv H.
              apply Nat.eqb_eq in HL1; apply Nat.eqb_eq in HL2; cbn in *.
              rewrite <- map_vect_list_app in HCaseCons1 by lia.
              specialize HCaseCons2 with (3 := HCaseCons1).
              spec_assert HCaseCons2.
              { apply Nat.eqb_eq. rewrite app_length. cbn.
                enough (fin_to_nat i' = S (fin_to_nat i)) by lia.
                now apply finSucc_opt_Some'. }
              spec_assert HCaseCons2.
              { apply Nat.eqb_eq. rewrite app_length. cbn. lia. }
              rewrite <- app_assoc in HCaseCons2. cbn in *. auto.
          }
          { intros tps HNil. TMSimp. now specialize H2 with (1 := HNil). }
        }
      }
    Qed.


    Definition DoActions_Loop_steps_nil := DoActions_Step_steps_nil.

    Fixpoint DoActions_Loop_steps_cons (i : Fin.t n) tps1 tps2 tp :=
      match tps2 with
      | nil => DoActions_Step_steps_cons i tps1 [] tp
      | tp' :: tps2' =>
        match finSucc_opt i with
        | None => 0 (* can't happen *)
        | Some i' =>
          1 + DoActions_Step_steps_cons i tps1 tps2 tp + DoActions_Loop_steps_cons i' (tps1 ++ [doAct tp acts[@i]]) tps2' tp'
        end
      end.

    Definition DoActions_Loop_T (i : Fin.t n) : tRel sigSim 1 :=
      fun tin k =>
        (exists tps1 tps2 tp,
            (length tps1 =? fin_to_nat i) = true /\
            (length tps1 + (1 + length tps2) =? n) = true /\
            atCons tin[@Fin0] tps1 tps2 tp /\
            DoActions_Loop_steps_cons i tps1 tps2 tp <= k) \/
        (exists tps, atNil tin[@Fin0] tps /\ DoActions_Loop_steps_nil <= k).

    Lemma DoActions_Loop_Terminates (i : Fin.t n) : projT1 (DoActions_Loop i) ↓ DoActions_Loop_T i.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold DoActions_Loop. TM_Correct.
        - apply DoActions_Step_Realise.
        - apply DoActions_Step_Terminates. }
      {
        revert i. apply StateWhileCoInduction; intros i; intros. destruct HT as [ (tps1&tps2&tp&HL1&HL2&HCons&Hk) | (tps&HNil&Hk) ].
        { (* cons case *)
          exists (DoActions_Step_steps_cons i tps1 tps2 tp). repeat split.
          { hnf. left. eauto 7. }
          intros ymid mmid (HStep_cons&HStep_nil). destruct ymid as [ i' | [] ].
          { (* continue case *) specialize HStep_cons with (1 := HL1) (2 := HL2) (3 := HCons).
            destruct tps2 as [ | tp' tps2']; cbn in *.
            - destruct HStep_cons as (?&?); congruence.
            - destruct HStep_cons as [HStep_cons HStep_cons']. destruct (finSucc_opt i) as [ iSucc | ] eqn:Ei; auto. inv HStep_cons'. rename iSucc into i'.
              eexists. split; eauto.
              { hnf. left. exists (tps1 ++ [doAct tp acts[@i]]), tps2', tp'. simpl_list. cbn. apply Nat.eqb_eq in HL1. apply Nat.eqb_eq in HL2.
                apply finSucc_opt_Some' in Ei. repeat split; auto; apply Nat.eqb_eq; lia. }
          }
          { (* false break case *) specialize HStep_cons with (1 := HL1) (2 := HL2) (3 := HCons).
            destruct tps2 as [ | tp' tps2']; cbn in *.
            - destruct HStep_cons as (HStep_cons&_). auto.
            - destruct HStep_cons as (?&?). destruct (finSucc_opt i); auto; congruence.
          }
        }
        { (* nil case *) exists (DoActions_Step_steps_nil). repeat split.
          { hnf. right. eauto. }
          intros ymid tmid (HStep_cons&HStep_nil). destruct ymid as [ i' | ]; cbn in *.
          - specialize HStep_nil with (1 := HNil) as (HStep_nil&HStep_nil'); inv HStep_nil'.
          - specialize HStep_nil with (1 := HNil) as (HStep_nil&HStep_nil'); inv HStep_nil'. auto.
        }
      }
    Qed.

    

    Definition DoActions_Rel : pRel sigSim unit 1 :=
      ignoreParam
        (fun tin tout =>
           forall (tps : list (tape sig)),
             (length tps =? n) = true ->
             atStart tin[@Fin0] tps ->
             atNil tout[@Fin0] (map_vect_list (@doAct _) acts tps)).


    Definition DoActions : pTM sigSim unit 1 :=
      match finMin_opt n with
      | None => Move Rmove (* Nothing to do, just move from the start to the nil symbol *)
      | Some i =>
        Move Rmove;; (* Move from start to first cons *)
        DoActions_Loop i
      end.

    Lemma DoActions_Realise : DoActions ⊨ DoActions_Rel.
    Proof.
      clear pM F.
      unfold DoActions.
      destruct (finMin_opt n) as [ i | ] eqn:E; swap 1 2.
      {
        eapply Realise_monotone.
        { TM_Correct. }
        {
          intros tin ([], tout) H. intros tps HL HStart. cbn in *. intros. TMSimp.
          unfold atStart in HStart. TMSimp.
          apply finMin_opt_None in E as ->.
          destruct tps; cbn in *; inv HL.
          hnf. cbn. reflexivity.
        }
      }
      {
        eapply Realise_monotone.
        { TM_Correct. apply DoActions_Loop_Realise. }
        {
          intros tin ([], tout) H. intros tps HL HStart. TMSimp.
          rename H0 into HLoop_Nil, H1 into HLoop_Cons. clear HLoop_Cons.
          pose proof finMin_opt_Some E as (n'&E').
          apply finMin_opt_Some_val in E. subst.
          destruct tps as [ | tp tps]; cbn in *. inv HL.
          specialize (HLoop_Nil nil tps tp).
          spec_assert HLoop_Nil by now rewrite E. spec_assert HLoop_Nil by auto. spec_assert HLoop_Nil.
          { cbn. unfold atStart in HStart. TMSimp. hnf. f_equal. now rewrite map_app, <- app_assoc. }
          destruct_vector. cbn. auto.
        }
      }
    Qed.


    Definition DoActions_steps (tps : list (tape sig)) : nat :=
      match finMin_opt n with
      | None => 1
      | Some i =>
        match tps with
        | nil => 0 (* can't happen *)
        | tp :: tps => 2 + DoActions_Loop_steps_cons i [] tps tp
        end
      end.
    
    Definition DoActions_T : tRel sigSim 1 :=
      fun tin k => exists tps, (length tps =? n) = true /\ atStart tin[@Fin0] tps /\ DoActions_steps tps <= k.

    Lemma DoActions_Terminates : projT1 DoActions ↓ DoActions_T.
    Proof.
      clear pM F.
      unfold DoActions. unfold DoActions_T, DoActions_steps. destruct (finMin_opt n) as [ i | ] eqn:Ei.
      { eapply TerminatesIn_monotone.
        { TM_Correct. apply DoActions_Loop_Terminates. }
        { intros tin k. intros (tps&HL&HStart&Hk). hnf in HStart. TMSimp.
          destruct tps as [ | tp tps]; cbn in *.
          { exfalso. clear acts Hk. destruct n; cbn in *; congruence. }
          exists 1, (DoActions_Loop_steps_cons i [] tps tp). repeat split; try lia.
          intros tmid () H. hnf. left. TMSimp. exists nil, tps, tp. cbn. rewrite (finMin_opt_Some_val Ei). repeat split; auto.
          hnf. now simpl_list.
        }
      }
      { eapply TerminatesIn_monotone. TM_Correct. now intros tin k (?&?&?&H). }
    Qed.

  End DoActions.


  Section Step.

    Variable (q : state (projT1 pM)).

    Definition Step_Rel : pRel sigSim (state (projT1 pM) + F) 1 :=
      fun tin '(yout, tout) =>
        forall (T : tapes sig n),
          tin[@Fin0] ≃ T ->
          if halt q
          then tout[@Fin0] ≃ T /\ yout = inr (projT2 pM q)
          else
            let c := {| cstate := q; ctapes := T |} in
            let (q', T') := step c in
            tout[@Fin0] ≃ T' /\ yout = inl q'.

    Definition Step : pTM sigSim (state (projT1 pM) + F) 1 :=
      if halt q
      then Return Nop (inr (projT2 pM q))
      else
        Switch ReadCurrentSymbols
               (fun (cs : Vector.t (option sig) n) =>
                  Return (MoveToStart;; DoActions (snd (trans (q, cs)));; MoveToStart) (inl (fst (trans (q, cs))))).

    Lemma Step_Realise : Step ⊨ Step_Rel.
    Proof.
      unfold Step, Step_Rel. destruct (halt q).
      { (* halting state *)
        eapply Realise_monotone.
        { TM_Correct. }
        { intros tin (yout, tout) H. intros T HEncT. TMSimp. eauto. }
      }
      { (* non-halting state *)
        eapply Realise_monotone.
        { eapply Switch_Realise.
          - apply ReadCurrentSymbols_Realise.
          - intros cs. TM_Correct.
            + apply MoveToStart_Realise.
            + apply DoActions_Realise.
            + apply MoveToStart_Realise. }
        {
          intros tin (yout, tout) H. intros T HEncT.
          unfold step. cbn. destruct (trans (q, current_chars T)) as [q' act] eqn:E'.
          TMSimp. rename H into HReadCurrenSymbols, H1 into HMoveToStart1, H2 into HDoActions, H3 into HMoveToStart2.
          specialize HReadCurrenSymbols with (1 := HEncT) as [HReadCurrenSymbols ->].
          specialize HMoveToStart1 with (1 := HReadCurrenSymbols).
          specialize HDoActions with (2 := HMoveToStart1). spec_assert HDoActions.
          { apply Nat.eqb_eq. apply vector_to_list_length. }
          specialize HMoveToStart2 with (1 := HDoActions).
          split.
          - eapply atStart_contains; eauto. now rewrite map_vect_list_length, vector_to_list_length.
            rewrite E'. cbn. now rewrite map_vect_list_eq.
          - rewrite E'. cbn. reflexivity.
        }
      }
    Qed.


    Definition Step_steps (T : tapes sig n) : nat :=
      let (q', act) := (trans (m := projT1 pM) (q, current_chars T)) in
      3 + ReadCurrentSymbols_steps T + MoveToStart_steps (vector_to_list T) + DoActions_steps act (vector_to_list T) + MoveToStart_steps (vector_to_list (doAct_multi T act)).

    Definition Step_T : tRel sigSim 1 :=
      fun tin k =>
        if halt q
        then True
        else exists (T : tapes sig n), tin[@Fin0] ≃ T /\ Step_steps T <= k.

    Lemma Step_Terminates : projT1 Step ↓ Step_T.
    Proof.
      unfold Step, Step_T. destruct (halt q).
      { eapply TerminatesIn_monotone.
        { TM_Correct. }
        { intros tin k _. lia. } }
      { eapply TerminatesIn_monotone.
        { unfold Step. apply Switch_TerminatesIn.
          - apply ReadCurrentSymbols_Realise.
          - apply ReadCurrentSymbols_Terminates.
          - intros cs. TM_Correct.
            + apply MoveToStart_Realise.
            + apply MoveToStart_Terminates.
            + apply DoActions_Realise.
            + apply DoActions_Terminates.
            + apply MoveToStart_Terminates.
        }
        {
          intros tin k (T&HEnc&Hk). unfold Step_steps in Hk. destruct (trans (m := projT1 pM) (q, current_chars T)) as (q'&act) eqn:E.
          exists (ReadCurrentSymbols_steps T), (2 + MoveToStart_steps (vector_to_list T) + DoActions_steps act (vector_to_list T) + MoveToStart_steps (vector_to_list (doAct_multi T act))).
          repeat split; try lia. hnf; eauto.
          intros tmid cs HReadCurrentSymbols. cbn in HReadCurrentSymbols. specialize HReadCurrentSymbols with (1 := HEnc) as (HReadCurrentSymbols&->).
          exists (MoveToStart_steps (vector_to_list T)), (1 + DoActions_steps act (vector_to_list T) + MoveToStart_steps (vector_to_list (doAct_multi T act))).
          repeat split; try lia. hnf; eauto.
          intros tmid0 [] HMoveToStart1. cbn in HMoveToStart1. specialize HMoveToStart1 with (1 := HReadCurrentSymbols).
          exists (DoActions_steps act (vector_to_list T)), (MoveToStart_steps (vector_to_list (doAct_multi T act))). repeat split; try lia.
          { hnf. eexists. repeat split. 2: eauto. apply Nat.eqb_eq, vector_to_list_length. rewrite E. cbn. reflexivity. }
          intros tmid1 [] HDoActions. cbn in HDoActions. specialize HDoActions with (2 := HMoveToStart1). spec_assert HDoActions by (apply Nat.eqb_eq, vector_to_list_length).
          { hnf. eexists. repeat split. 2: eauto. rewrite map_vect_list_eq in HDoActions. now rewrite E in HDoActions. }
        }
      }
    Qed.

  End Step.

  Section Loop.

    Definition Loop := StateWhile Step.

    Definition Loop_Rel q : pRel sigSim F 1 :=
      fun tin '(yout, tout) =>
        forall (T : tapes sig n),
          tin[@Fin0] ≃ T ->
          let c := {| cstate := q; ctapes := T |} in
          exists c' k, loopM c k = Some c' /\
                  tout[@Fin0] ≃ ctapes c' /\ yout = projT2 pM (cstate c').

    Lemma Loop_Realise q : Loop q ⊨ Loop_Rel q.
    Proof.
      eapply Realise_monotone.
      { unfold Loop. eapply StateWhile_Realise. apply Step_Realise. }
      {
        apply StateWhileInduction; intros; intros T HEncT; TMSimp.
        - modpon HLastStep. unfold haltConf in *; cbn in *. destruct (halt l) eqn:E.
          + destruct HLastStep as [HLastStep HLastStep']; inv HLastStep'.
            eexists; exists 0. cbn. unfold haltConf; cbn. rewrite E. repeat split; eauto.
          + destruct (step _). destruct HLastStep as [_ ?]; congruence.
        - modpon HStar. unfold haltConf in *; cbn in *. destruct (halt l) eqn:E.
          + destruct HStar as [HStar HStar']; inv HStar'.
          + destruct (step _) as [q' T'] eqn:E'. destruct HStar as [HStar HStar']; inv HStar'.
            modpon HLastStep. destruct HLastStep as (c'&k&HLastStep&HLastStep'&->).
            eexists. exists (S k). cbn. unfold haltConf in *; cbn in *. rewrite E, E'. repeat split; eauto.
      }
    Qed.


    Fixpoint Loop_steps q (T : tapes sig n) (k : nat) {struct k} :=
      if halt q
      then 0
      else match k with
           | 0 => 0 (* can't happen *)
           | S k' =>
             let (q', acts) := trans (m := projT1 pM) (q, current_chars T) in
             1 + Step_steps q T + Loop_steps q' (doAct_multi T acts) k'
           end.

    Lemma Loop_steps_eq q T k :
      Loop_steps q T k =
      if halt q
      then 0
      else match k with
           | 0 => 0
           | S k' =>
             let (q', acts) := trans (m := projT1 pM) (q, current_chars T) in
             1 + Step_steps q T + Loop_steps q' (doAct_multi T acts) k'
           end.
    Proof. destruct k; auto. Qed.
      

    Definition Loop_T q : tRel sigSim 1 :=
      fun tin k =>
        exists T kn outc,
          loopM (mk_mconfig q T) kn = Some outc /\
          tin[@Fin0] ≃ T /\
          Loop_steps q T kn <= k.

    Local Arguments doAct_multi : simpl never.

    Lemma Loop_Terminates q : projT1 (Loop q) ↓ Loop_T q.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold Loop. TM_Correct.
        - apply Step_Realise.
        - apply Step_Terminates. }
      { revert q. apply StateWhileCoInduction; intros q; intros. destruct HT as (T&kn&outc&HLoop&HEncT&Hk). rewrite Loop_steps_eq in Hk. unfold Step_T, Step_Rel.
        destruct (halt q) eqn:E; cbn in *.
        - exists 0. split; auto. intros ymid tmid HStep. specialize HStep with (1 := HEncT) as (HStep&->). auto.
        - destruct kn as [ | kn']; cbn in *.
          + unfold haltConf in HLoop. cbn in HLoop. rewrite E in HLoop. congruence.
          + unfold haltConf in HLoop. cbn in HLoop. rewrite E in HLoop.
            destruct (trans (q, current_chars T)) as [q' acts] eqn:E2.
            exists (Step_steps q T). repeat split. eauto.
            intros ymid tmid HStep. specialize HStep with (1 := HEncT).
            assert (step (mk_mconfig q T) = mk_mconfig q' (doAct_multi T acts)) as Hstep.
            { unfold step. cbn. rewrite E2. reflexivity. }
            rewrite Hstep in HStep. destruct HStep as (HStep&->).
            exists (Loop_steps q' (doAct_multi T acts) kn'). repeat split; auto.
            hnf. do 3 eexists. repeat split. 2: eauto. rewrite <- Hstep. eauto. eauto.
      }
    Qed.

    
    Definition ToSingleTape := Loop (start (projT1 pM)).

    Definition ToSingleTape_Rel := Loop_Rel (start (projT1 pM)).

    Lemma ToSingleTape_Realise : ToSingleTape ⊨ ToSingleTape_Rel.
    Proof. exact (@Loop_Realise (start (projT1 pM))). Qed.

    Definition ToSingleTape_T := Loop_T (start (projT1 pM)).

    Lemma ToSingleTape_Terminates : projT1 ToSingleTape ↓ ToSingleTape_T.
    Proof. exact (@Loop_Terminates (start (projT1 pM))). Qed.


    Variable M_R : pRel sig F n.

    Definition ToSingleTape_Rel' : pRel sigSim F 1 :=
      fun tin '(yout, tout) =>
        forall T, tin[@Fin0] ≃ T ->
             exists T', M_R T (yout, T') /\ tout[@Fin0] ≃ T'.
      
    Corollary ToSingleTape_Realise' :
      pM ⊨ M_R ->
      ToSingleTape ⊨ ToSingleTape_Rel'.
    Proof.
      intros M_Realise.
      eapply Realise_monotone.
      { apply ToSingleTape_Realise. }
      {
        intros tin (yout, tout) H. cbn in *.
        hnf in M_Realise.
        intros T HEncT. specialize H with (1 := HEncT) as (c'&k&HLoop&HEncT'&->).
        specialize M_Realise with (1 := HLoop). exists (ctapes c'). auto.
      }
    Qed.


    Variable M_T : tRel sig n.

    Definition ToSingleTape_T' : tRel sigSim 1 :=
      fun tin k => exists T k', tin[@Fin0] ≃ T /\ M_T T k' /\ Loop_steps (start (projT1 pM)) T k' <= k.

    Corollary ToSingleTape_Terminates' :
      projT1 pM ↓ M_T ->
      projT1 ToSingleTape ↓ ToSingleTape_T'.
    Proof.
      intros HTerm. eapply TerminatesIn_monotone.
      { apply ToSingleTape_Terminates. }
      { intros tin k (T&kn&HEncT&HT&Hk). hnf. hnf in HTerm. specialize HTerm with (1 := HT) as (oconf&HLoop). do 3 eexists. repeat split; eauto. }
    Qed.

  End Loop.

End ToSingleTape.
