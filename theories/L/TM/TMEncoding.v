From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd.
From Undecidability.L.Computability Require Import MuRec.
Require Import List Init.Nat.

From Undecidability Require Import TM.TM.
Require Import PslBase.FiniteTypes.FinTypes.

(** ** Extraction of Turing Machine interpreter  *)

(** *** Encoding finite types *)
(* This is not an instance because we only want it for very specific types. *)
Definition registered_finType `{X : finType} : registered X.
Proof.
  eapply (registerAs index).
  intros x y H. now apply injective_index.
Defined.

Definition finType_eqb {X:finType} (x y : X) :=
  Nat.eqb (index x) (index y).

Lemma finType_eqb_reflect (X:finType) (x y:X) : reflect (x = y) (finType_eqb x y).
Proof.
  unfold finType_eqb. destruct (Nat.eqb_spec (index x) (index y));constructor.
  -now apply injective_index.
  -congruence.
Qed.

Section finType_eqb.
  Local Existing Instance registered_finType.

  Global Instance term_index (F:finType): computableTime (@index F) (fun _ _=> (1, tt)).
  Proof.
    apply cast_computableTime.
  Qed.

  Global Instance term_eqb (X:finType) : computableTime (finType_eqb (X:=X)) (fun x _ => (1,fun y _ => (17 * Init.Nat.min (index x) (index y) + 17,tt))).
  Proof.
    extract.
    solverec.
  Qed.
End finType_eqb.



Section Lookup.
  Variable X Y : Type.
  Variable eqb : X -> X -> bool.

  Fixpoint lookup (x:X) (A:list (X*Y)) d: Y :=
    match A with
      [] => d
    | (key,Lproc)::A =>
      if eqb x key then Lproc else lookup x A d
    end.

End Lookup.

Section funTable.

  Variable X : finType.
  Variable Y : Type.
  Variable f : X -> Y.

  Definition funTable :=
    map (fun x => (x,f x)) (elem X).

  Variable (eqb : X -> X -> bool).
  Variable (Heqb:forall x y, reflect (x = y) (eqb x y)).

  Lemma lookup_funTable x d:
    lookup eqb x funTable d = f x.
  Proof.
    unfold funTable.
    specialize (elem_spec x).
    generalize (elem X) as l.
    induction l;cbn;intros Hel.
    -tauto.
    -destruct (Heqb x a).
     +congruence.
     +destruct Hel. 1:congruence.
      eauto.
  Qed.
End funTable.

Definition lookupTime {X Y} `{registered X} (eqbT : timeComplexity (X ->X ->bool)) x (l:list (X*Y)):=
  fold_right (fun '(a,b) res => callTime2 eqbT x a + res +19) 4 l.


Global Instance term_lookup X Y `{registered X} `{registered Y}:
  computableTime (@lookup X Y) (fun eqb T__eqb => (1, fun x _ => (5, fun l _ => (1, fun d _ => (lookupTime T__eqb x l,tt))))).
extract. unfold lookupTime. solverec.
Qed.

Lemma lookupTime_leq {X Y} `{registered X} (eqbT:timeComplexity (X -> X -> bool)) x (l:list (X*Y)) k:
  (forall y, callTime2 eqbT x y <= k)
  -> lookupTime eqbT x l <= length l * (k + 19) + 4.
Proof.
  intros H'.
  induction l as [ | [a b] l].
  -cbn. omega.
  -unfold lookupTime. cbn [fold_right]. fold (lookupTime eqbT x l).
   setoid_rewrite IHl. cbn [length]. rewrite H'.
   ring_simplify. omega.
Qed.

(** *** Encoding vectors *)

Instance register_vector X `{registered X} n : registered (Vector.t X n).
Proof.
  apply (registerAs VectorDef.to_list).
  intros x. induction x.
  - intros y. pattern y. revert y. eapply VectorDef.case0. cbn. reflexivity.
  - intros y. clear H. revert h x IHx. pattern n, y. revert n y.
    eapply Vector.caseS. intros h n y h0 x IHx [=].
    subst. f_equal. eapply IHx. eassumption.
Defined.

Instance term_to_list X `{registered X} n : computableTime (Vector.to_list (A:=X) (n:=n)) (fun _ _ => (1,tt)).
Proof.
  apply cast_computableTime.
Qed.

Definition to_list := @Vector.to_list.

Instance term_vector_map X Y `{registered X} `{registered Y} n (f:X->Y) fT:
  computableTime f fT ->
  computableTime (VectorDef.map f (n:=n))
                 (fun l _ => (List.fold_right (fun (x0 : X) (res : nat) => fst (fT x0 tt) + res + 12) 8 l + 3,tt)).
Proof.
  intros ?.
  computable_casted_result.
  apply computableTimeExt with (x:= fun x => map f (to_list x)).
  2:{
    extract.
    solverec.
  }

  cbn. intros x.
  clear - x.
  induction n. revert x. apply VectorDef.case0. easy. revert IHn. apply Vector.caseS' with (v:=x).
  intros. cbn. f_equal. fold (Vector.fold_right (A:=X) (B:=Y)).
  setoid_rewrite IHn. reflexivity.
Qed.

(* Instance term_vector_map X Y `{registered X} `{registered Y} n (f:X->Y): computable f -> computable (VectorDef.map f (n:=n)). *)
(* Proof. *)
(*   intros ?. *)

(*   internalize_casted_result. *)
(*   apply computableExt with (x:= fun x => map f (Vector.to_list x)). *)
(*   2:{ *)
(*     extract. *)
(*   } *)

(*   cbn. intros x.  *)
(*   clear - x. *)
(*   induction n. revert x. apply VectorDef.case0. easy. revert IHn. apply Vector.caseS' with (v:=x). *)
(*   intros. cbn. f_equal. fold (Vector.fold_right (A:=X) (B:=Y)). *)
(*   setoid_rewrite IHn. reflexivity. *)
(* Qed. *)

Fixpoint time_map2 {X Y Z} `{registered X} `{registered Y} `{registered Z} (gT : timeComplexity (X->Y->Z)) (l1 :list X) (l2 : list Y) :=
  match l1,l2 with
  | x::l1,y::l2 => callTime2 gT x y + 18 + time_map2 gT l1 l2
  | _,_ => 9
  end.
Instance term_map2 n A B C `{registered A} `{registered B} `{registered C} (g:A -> B -> C) gT:
  computableTime g gT-> computableTime (Vector.map2 g (n:=n)) (fun l1 _ => (1,fun l2 _ => (time_map2 gT (Vector.to_list l1) (Vector.to_list l2) +8,tt))).
Proof.
  intros ?.
  computable_casted_result.
  pose (f:=(fix f t a : list C:=
              match t,a with
                t1::t,a1::a => g t1 a1 :: f t a
              | _,_ => []
              end)).
  assert (computableTime f (fun l1 _ => (5,fun l2 _ => (time_map2 gT l1 l2,tt)))).
  {subst f; extract.



   solverec. }
  apply computableTimeExt with (x:= fun t a => f (Vector.to_list t) (Vector.to_list a)).
  2:{extract. solverec. }
  induction n;cbn.
  -do 2 destruct x using Vector.case0. reflexivity.
  -destruct x using Vector.caseS'. destruct x0 using Vector.caseS'.
   cbn. f_equal. apply IHn.
Qed.


Lemma time_map2_leq X Y Z `{registered X}  `{registered Y}  `{registered Z}  (fT:timeComplexity (X -> Y -> Z))(l1 : list X) (l2:list Y) k:
  (forall x y, callTime2 fT x y <= k) ->
  time_map2 fT l1 l2<= length l1 * (k+18) + 9.
Proof.
  intros H';
    induction l1 in l2|-*;cbn [time_map2].
  -intuition.
  -destruct l2;ring_simplify. intuition.
   rewrite H',IHl1. cbn [length]. ring_simplify. intuition.
Qed.


Run TemplateProgram (tmGenEncode "move_enc" move).
Hint Resolve move_enc_correct : Lrewrite.

Section fix_sig.
  Variable sig : finType.
  Context `{reg_sig : registered sig}.

  (** *** Encoding Tapes *)
  Section reg_tapes.
    Implicit Type (t : TM.tape sig).

    Run TemplateProgram (tmGenEncode "tape_enc" (TM.tape sig)).
    Hint Resolve tape_enc_correct : Lrewrite.

    (**Internalize constructors **)

    Global Instance term_leftof : computableTime (@leftof sig) (fun _ _ => (1, fun _ _ => (1,tt))).
    Proof.
      extract constructor.
      solverec.
    Qed.

    Global Instance term_rightof : computableTime (@rightof sig) (fun _ _ => (1, fun _ _ => (1,tt))).
    Proof.
      extract constructor. solverec.
    Qed.

    Global Instance term_midtape : computableTime (@midtape sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (1,tt)))).
    Proof.
      extract constructor. solverec.
    Qed.

    Global Instance term_tape_move_left' : computableTime (@tape_move_left' sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (12,tt)))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_left : computableTime (@tape_move_left sig) (fun _ _ => (23,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_right' : computableTime (@tape_move_right' sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (12,tt)))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_right : computableTime (@tape_move_right sig) (fun _ _ => (23,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move : computableTime (@tape_move sig) (fun _ _ => (1,fun _ _ => (48,tt))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_left : computableTime (@left sig) (fun _ _ => (10,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_right : computableTime (@right sig) (fun _ _ => (10,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_write : computableTime (@tape_write sig) ((fun _ _ => (1,fun _ _ => (28,tt)))).
    Proof.
      extract. solverec.
    Qed.

  End reg_tapes.

  Definition mconfigAsPair {B : finType} {n} (c:mconfig sig B n):= let (x,y) := c in (x,y).

  Global Instance registered_mconfig (B : finType) `{registered B} n: registered (mconfig sig B n).
  Proof.
    eapply (registerAs mconfigAsPair). clear.
    register_inj.
  Defined.

  Global Instance term_mconfigAsPair (B : finType) `{registered B} n: computableTime (@mconfigAsPair B n) (fun _ _ => (1,tt)).
  Proof.
    apply cast_computableTime.
  Qed.

End fix_sig.

Section fix_sig2.

  Variable sig : finType.
  Context `{reg_sig : registered sig}.

  Global Instance term_cstate (B : finType) `{registered B} n: computableTime (@cstate sig B n) (fun _ _ => (7,tt)).
  Proof.
    apply computableTimeExt with (x:=fun x => fst (mconfigAsPair x)).
    2:{ extract. solverec. }
    intros [];reflexivity.
  Qed.

  Global Instance term_ctapes (B : finType) `{registered B} n: computableTime (@ctapes sig B n) (fun _ _ => (7,tt)).
  Proof.
    apply computableTimeExt with (x:=fun x => snd (mconfigAsPair x)).
    2:{extract. solverec. }
    intros [];reflexivity.
  Qed.

  Global Instance registered_mk_mconfig (B : finType) `{registered B} n: computableTime (@mk_mconfig sig B n) (fun _ _ => (1,fun _ _ => (3,tt))).
  Proof.
    computable_casted_result.
    extract. solverec.
  Qed.
End fix_sig2.


(* Fixpoint time_loop f fT p pT := cnst 1. *)

Definition Halt' Sigma n (M: mTM Sigma n) (start: mconfig Sigma (states M) n) :=
  exists (f: mconfig _ (states M) _), halt (cstate f)=true /\ exists k, loopM start k = Some f.

Definition Halt :{ '(Sigma, n) : _ & mTM Sigma n & tapes Sigma n} -> _ :=
  fun '(existT2 (Sigma, n) M tp) =>
    exists (f: mconfig _ (states M) _), halt (cstate f) = true
                                   /\ exists k, loopM (mk_mconfig (start M) tp) k = Some f.

Hint Resolve tape_enc_correct : Lrewrite.

Fixpoint loopTime {X} `{registered X} f (fT: timeComplexity (X -> X)) (p: X -> bool) (pT : timeComplexity (X -> bool)) (a:X) k :=
  fst (pT a tt) +
  match k with
    0 => 7
  |  S k =>
     fst (fT a tt) + 13 + loopTime f fT p pT (f a) k
  end.

Instance term_loop A `{registered A} :
  computableTime (@loop A)
                 (fun f fT => (1,fun p pT => (1,fun a _ => (5,fun k _ =>(loopTime f fT p pT a k,tt))))).
Proof.
  extract.
  solverec.
Qed.

Require Import Vector Undecidability.L.Datatypes.LOptions.

Section loopM.
  Context (sig : finType).
  Let reg_sig := @registered_finType sig.
  Existing Instance reg_sig.
  Variable n : nat.
  Variable M : mTM sig n.

  Let reg_states := @registered_finType (states M).
  Existing Instance reg_states.


  Instance term_vector_eqb X `{registered X} (n' m:nat) (eqb:X->X->bool) eqbT:
    computableTime eqb eqbT
    -> computableTime
        (VectorEq.eqb eqb (A:=X) (n:=n') (m:=m))
        (fun A _ => (1,fun B _ => (list_eqbTime eqbT (Vector.to_list A) (Vector.to_list B) + 9,tt))).
  Proof.
    intros ?.
    apply computableTimeExt with (x:=(fun x y => list_eqb eqb (Vector.to_list x) (Vector.to_list y))).
    2:{extract.
       solverec. }
    intros v v'. hnf.
    induction v in n',v'|-*;cbn;destruct v';cbn;try tauto. rewrite <- IHv. f_equal.
  Qed.


  Lemma to_list_length X n0 (l:Vector.t X n0) :length l = n0.
  Proof.
    induction l. reflexivity. rewrite <- IHl at 3. reflexivity.
  Qed.

  Definition transTime := (length (elem (states M) )*17 + n * 17 * (length ( elem sig )+ 4) + 71) * length (funTable (trans (m:=M))) + 16.

  (** *** Computability of transition relation *)
  Instance term_trans : computableTime (trans (m:=M)) (fun _ _ => (transTime,tt)).
  Proof.
    pose (t:= (funTable (trans (m:=M)))).
    apply computableTimeExt with (x:= fun c => lookup (prod_eqb finType_eqb (Vector.eqb (option_eqb finType_eqb))) c t (start M,Vector.const (None,N) _)).
    2:{extract.
       cbn [fst snd]. intuition ring_simplify.


       rewrite lookupTime_leq with (k:=(17* length (elem (states M)) + 17 * n * (length (elem sig) + 4) + 52)).
       -unfold transTime.

        repeat match goal with
                 |- context C[length _] =>let G:= context C [length t] in progress change G
               end.
        ring_simplify.  omega.
       -intros y. unfold callTime2.
        cbn [fst snd]. ring_simplify.
        setoid_rewrite index_leq at 1 2. rewrite Nat.min_id.
        rewrite list_eqbTime_leq with (k:= | elem sig| * 17 + 29).
        +rewrite to_list_length. ring_simplify. omega.
        +intros [] [];unfold callTime2;cbn [fst snd].
         setoid_rewrite index_leq at 1 2. rewrite Nat.min_id.
         all:ring_simplify. all:omega.
    }
    cbn -[t] ;intro. subst t.  setoid_rewrite lookup_funTable. reflexivity.
    apply prod_eqb_spec. apply finType_eqb_reflect. apply vector_eqb_spec,LOptions.option_eqb_spec,finType_eqb_reflect.
  Qed.

  Instance term_current: computableTime ((current (sig:=sig))) (fun _ _ => (10,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  Instance term_current_chars: computableTime (current_chars (sig:=sig) (n:=n))  (fun _ _ => (n * 22 +12,tt)).
  Proof.
    extract.
    solverec.
    assert (H1:forall X (l:list X), List.fold_right (fun _ (res : nat) => 10 + res + 12) 8 l = length l * 22 +8).
    {induction l;ring_simplify;cbn [List.fold_right length]. now intuition.
     rewrite IHl.  omega. }
    rewrite H1,to_list_length.  omega.
  Qed.

  Definition step' (c :  mconfig sig (states M) n) : mconfig sig (states M) n :=
    let (news, actions) := trans (cstate c, current_chars (ctapes c)) in
    mk_mconfig news (doAct_multi (ctapes c) actions).


  Instance term_doAct: computableTime (doAct (sig:=sig)) (fun _ _ => (1,fun _ _ => (89,tt))).
  Proof.
    extract.
    solverec.
  Qed.

  Instance term_doAct_multi: computableTime (doAct_multi (n:=n) (sig:=sig)) (fun _ _ => (1,fun _ _ =>(n * 108 + 19,tt))).
  Proof.
    extract.
    solverec.
    rewrite time_map2_leq with (k:=90).
    2:now solverec.
    solverec. now rewrite to_list_length.
  Qed.


  Instance term_step' : computableTime (step (M:=M)) (fun _ _ => (n* 130+ transTime + 64,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  Definition haltTime := length (funTable (halt (m:=M))) * (length (elem (states M)) * 17 + 37) + 12.

  Instance term_halt : computableTime (halt (m:=M)) (fun _ _ => (haltTime,tt)).
  Proof.
    pose (t:= (funTable (halt (m:=M)))).
    apply computableTimeExt with (x:= fun c => lookup finType_eqb c t false).
    2:{extract.
       solverec.
       rewrite lookupTime_leq with (k:=17 * (| elem (states M) |) + 18).
       2:{
         intros. cbn [callTime2 fst].
         repeat rewrite index_leq. rewrite Nat.min_id. omega.
       }
       unfold haltTime. subst t.
       ring_simplify. reflexivity.
    }
    cbn;intro. subst t. setoid_rewrite lookup_funTable. reflexivity.
    apply finType_eqb_reflect.
  Qed.

  Instance term_haltConf : computableTime (haltConf (M:=M)) (fun _ _ => (haltTime+8,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  (** *** Computability of step-ndexed interpreter *)
  Global Instance term_loopM :
    let c1 := (haltTime + n*130 + transTime + 85) in
    let c2 := 15 + haltTime in
    computableTime (loopM (M:=M)) (fun _ _ => (5,fun k _ => (c1 * k + c2,tt))).
  Proof.
    unfold loopM. (* as loop is already an registered instance, this here is a bit out of the scope. Therefore, we unfold manually here. *)
    extract.
    solverec. 
  Qed.

  Instance term_test cfg :
    computable (fun k => LOptions.isSome (loopM (M := M) cfg k)).
  Proof.
    extract.
  Qed.

  Lemma Halt_red cfg :
    Halt' cfg <-> converges (mu (ext ((fun k => LOptions.isSome (loopM (M := M) cfg k))))).
  Proof.
    split; intros.
    - destruct H as (f & ? & k & ?).
      edestruct (mu_complete).
      + eapply term_test.
      + intros. eexists. rewrite !ext_is_enc. now Lsimpl.
      + Lsimpl. now rewrite H0.
      + exists (ext x). split. eauto. Lproc.
    - destruct H as (v & ? & ?). edestruct mu_sound as (k & ? & ? & _).
      + eapply term_test.
      + intros. eexists. now Lsimpl.
      + eassumption.
      + eauto.
      + subst.
        assert ((ext (fun k : nat => LOptions.isSome (loopM cfg k))) (ext k) ==
                ext (LOptions.isSome (loopM cfg k))) by Lsimpl.
        rewrite H1 in H2. clear H1.
        eapply unique_normal_forms in H2; try Lproc. eapply inj_enc in H2.
        destruct (loopM cfg k) eqn:E.
        * exists m. split. 2: eauto.
          unfold loopM in E. now eapply loop_fulfills in E.
        * inv H2.
  Qed.

End loopM.
