From Undecidability Require Import L.Datatypes.LBool L.Datatypes.Lists L.Tactics.LTactics L.Tactics.GenEncode L.Util.L_facts.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools LM_heap_def WriteValue CaseList Copy ListTM  JumpTargetTM WriteValue.
From Undecidability.TM.L Require Import Alphabets HeapInterpreter.StepTM M_LHeapInterpreter.
From Undecidability Require Import TM.TM L.AbstractMachines.FlatPro.LM_heap_correct.

From Undecidability Require Import L.L TM.TM.
Require Import List.
Import ListNotations.


Import VectorNotations.

From Undecidability.TM.L Require Import Compiler_spec Compiler_facts UnfoldHeap.

Require Import Equations.Prop.DepElim.


Set Default Proof Using "Type".

Section APP_right.

  Definition APP_right : pTM (sigPro)^+ unit 2 :=
    App_Commands;;
    (LiftTapes (WriteValue (encode [appT]%list)) [|Fin1|]);;
    App_Commands.

  Lemma APP_right_realises :
    Realise APP_right (fun t '(r, t') =>
    forall s1 s2 : L.term,
    t[@Fin0] ≃ compile s1
    -> t[@Fin1] ≃ compile s2
    -> t'[@Fin0] ≃ compile (L.app s1 s2)
      /\ isVoid (t'[@Fin1])).
  Proof.
    eapply Realise_monotone.
    {unfold APP_right. TM_Correct. all: apply App_Commands_Realise. }
    hnf. intros ? [] ? s1 s2. intros;TMSimp.
    specialize H2 with (x:=[appT]%list).
    modpon H. modpon H2. modpon H3.
    split. 2:solve [isVoid_mono].
    contains_ext. now autorewrite with list.
  Qed.  

End APP_right.

From Undecidability Require Import TM.L.Boollist_to_Enc.
From Undecidability Require Import encTM_boolList.


Section mk_init_one.

  Variable Σ : finType.

  Variable s b : Σ^+.
  Variable (retr_pro : Retract sigPro Σ).
  Variable (retr_list : Retract (sigList bool) Σ).

  Variable (H_disj : s <> b).


   (* Tapes: 
       0: bs (input, encTM)
       1: ter (input) 
       2: intern, bs als listBool
       3: intern 
       4: intern 
       5: intern 
     *)
  

  Definition M_init_one : pTM (Σ) ^+ unit 6:= 
    encTM2boolList.M s retr_list @[|Fin0;Fin3|];;
    Rev _ ⇑ retr_list @ [|Fin3;Fin2;Fin4|];;
    BoollistToEnc.M retr_list retr_pro @[|Fin2;Fin3;Fin4;Fin5|];;
    APP_right ⇑ retr_pro  @[|Fin1;Fin3|].

  Lemma M_init_one_realises :
    Realise M_init_one (fun t '(r, t') =>
                          forall (bs:list bool) (ter : L.term),
                            t[@Fin0] = encTM s b bs ->
                            t[@Fin1] ≃ compile ter ->
                            isVoid (t[@Fin2]) ->
                            isVoid (t[@Fin3]) ->
                            isVoid (t[@Fin4]) ->
                            isVoid (t[@Fin5]) ->
                            t'[@Fin0] = t[@Fin0] 
                            /\ t'[@Fin1] ≃ compile (L.app ter (encL bs))
                            /\ isVoid (t[@Fin2])/\ isVoid (t[@Fin3])/\ isVoid (t[@Fin4])/\ isVoid (t[@Fin5])).
  Proof using H_disj.
    eapply Realise_monotone.
    {
      unfold M_init_one. TM_Correct.
      -apply encTM2boolList.Realise. exact H_disj.
      -apply Rev_Realise.      
      -apply BoollistToEnc.Realise.     
      -apply APP_right_realises.
      (* -apply Reset_Realise with (X:=Pro). *)
    }
    intros ? [] ? bs s2. TMSimp.
    modpon H. modpon H0. modpon H2. modpon H4.
    rewrite rev_involutive in H4.
    easy.  
  Qed.  

End  mk_init_one.

Section mk_init.

  Variable Σ : finType.
  Variable s b : Σ^+.

  Variable (retr_closs : Retract (sigList (sigHClos)) Σ).

  Variable n : nat.

  Variable output1 : Fin.t n.
  Variable output2 : Fin.t n.
  Variable output3 : Fin.t n.
  Variable help1 : Fin.t n.
  Variable help2 : Fin.t n.

  Variable sim : term.

  Definition M_init k : pTM (Σ) ^+ unit (n + k). 
  Proof using All.
  (*   induction k as [ | k_ M_init]. *)
  (*   - exact (LiftTapes (WriteValue (encode (compile sim))) [| Fin.R ( k + 1) (help1) |]). *)
  (*   - refine ( *)
  (*         LiftTapes (M_init_one s b) [| Fin0 ; Fin.R (S k_ + 3) Fin0 ; Fin.R (S k_ + 3) Fin1 |] ;; *)
  (*         LiftTapes M_init (tabulate Fin.FS) *)
  (*       ). *)
  (* Defined. *)
  Admitted.

  Theorem M_init_rel k :
    Realise (M_init k) (fun t '(r, t') =>
                 forall (v:Vector.t (list bool) k), 
                   t = Vector.const niltape n ++ Vector.map (encTM s b) v ->
                   t'[@Fin.L k output1] ≃ [(0, compile (Vector.fold_left (fun s l_i => L.app s (encL l_i)) sim v))]%list /\
                   t'[@Fin.L k output2] ≃ []%list /\
                   t'[@Fin.L k output3] ≃ []%list
                   ).
  Proof.
    induction k.
    - (* cbn. eapply Realise_monotone. TM_Correct. *)
      (* intros t [[] t'] [H1 H2] v ->. *)
      (* destruct_tapes. cbn in *. *)
      (* admit. *)
  Admitted.

End mk_init.

Section conv_output.

  Variable Σ : finType.
  Variable s b : Σ^+.
  Variable (retr_pro : Retract sigPro Σ).

    

  Definition M_out : pTM (Σ) ^+ unit 2. Admitted.

  Theorem M_out_realise :
    Realise M_out (fun t '(r, t') =>
                     forall l : list bool, t[@Fin0] ≃ compile (list_enc l) ->
                        t[@Fin1] = niltape ->
                        t'[@Fin1] = encTM s b l).
  Admitted.

End conv_output.

Section MK_isVoid.

  Context {Σ : finType}.

  Definition MK_isVoid : pTM Σ unit 1.
  Admitted.

  Lemma MK_isVoid_realise :
    Realise MK_isVoid (fun t '(r, t') => isVoid (t'[@Fin0])).
  Admitted.

End MK_isVoid.

Section main.

  Variable k : nat.
  Variable (R : Vector.t (list bool) k -> (list bool) -> Prop).

  Variable s : term.

  Variable Hs1 : (forall v, forall m : list bool,
   R v m <->
   L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encL n)) s v) (encL m)).

  Variable Hs2 : (forall v, forall o : term,
                     L.eval (Vector.fold_left (n := k) (fun (s0 : term) (n : list bool) => L.app s0 (encL n)) s v) o ->
                     exists m : list bool, o = encL m).

  Axiom todo : forall {A : Type}, A.

  Definition n_main := 14.

  Definition Σ : Type := (sigStep + bool + sigList (sigPair sigHClos sigNat)).

  Definition retr_closs : Retract (sigList sigHClos) Σ := ComposeRetract _ M_LHeapInterpreter.retr_closures_step.
  Definition retr_clos : Retract sigHClos Σ := ComposeRetract retr_closs _.
  Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos _.

  Definition sym_s : Σ^+ := inr (inl (inr true)).
  Definition sym_b : Σ^+ := inr (inl (inr false)).

  (*
    auxiliary tapes:

    0    : T
    1    : V
    2    : H
    3-4  : aux for init
    5-12 : aux for loop
    13   : t
   *)

  Notation aux n := (Fin.L k (Fin.R 1 n)).

  Definition garb : Σ^+ := inl UNKNOWN.

  Definition M_main : pTM (Σ ^+)  unit (1 + n_main + k).
  Proof using k s.
    notypeclasses refine (
        M_init sym_s sym_b _ Fin1 Fin2 Fin3 Fin4 Fin5 s k ;;
        LiftTapes MK_isVoid [|aux Fin5 |] ;;
        LiftTapes MK_isVoid [|aux Fin6 |] ;;
        LiftTapes MK_isVoid [|aux Fin7 |] ;;
        LiftTapes MK_isVoid [|aux Fin8 |] ;;
        LiftTapes MK_isVoid [|aux Fin9 |] ;;
        LiftTapes MK_isVoid [|aux Fin10 |] ;;
        LiftTapes MK_isVoid [|aux Fin11 |] ;;
        LiftTapes MK_isVoid [|aux Fin12 |] ;;
        LiftAlphabet (LiftTapes Loop [| aux Fin0 ; aux Fin1 ; aux Fin2 ; aux Fin5 ; aux Fin6 ; aux Fin7 ; aux Fin8 ; aux Fin9 ; aux Fin10 ; aux Fin11 ; aux Fin12 |]) _ (inl UNKNOWN)  ;;
        CaseList _ ⇑ _ @ [| aux Fin1;aux Fin13 |];;
        UnfoldHeap.M _ _ retr_clos @ [| aux Fin13;aux Fin2;aux Fin5;aux Fin6;aux Fin7;aux Fin8;aux Fin9;aux Fin10;aux Fin11;aux Fin12|];;
        (LiftTapes (M_out sym_s sym_b _) [|(aux Fin13);Fin0|])
      ).
      all:exact _.
  Defined.

  Lemma syms_diff : sym_s <> sym_b. Proof. cbv. congruence. Qed.

  Lemma M_main_realise :
    Realise M_main (fun t '(r, t') =>
                      forall v,
                      t = const niltape (S n_main) ++ Vector.map (encTM sym_s sym_b) v  ->
                      exists m, 
                        t'[@ Fin0] = encTM sym_s sym_b m /\ R v m).
  Proof.
    eapply Realise_monotone.
    {
      unfold M_main.
      TM_Correct.
      all:eauto 8 using M_init_rel, MK_isVoid_realise, Loop_Realise, UnfoldHeap.Realise, M_out_realise, UnfoldHeap.Realise.
    }
    cbn.
    intros tin ([] & tout) H v ?. subst tin. 
    unfold n_main in *.   
    TMSimp.
    
    
    Set Nested Proofs Allowed.

    
    

    
    Fixpoint not_indexb {n} (v : list (Fin.t n)) (i : Fin.t n) {struct v}: bool :=
      match v with
       []%list => true
      | (i'::v)%list => if Fin.eqb i' i then false else not_indexb v i
      end.

    Lemma not_index_reflect n m (v : Vector.t _ m) (i : Fin.t n):
    not_index v i <-> not_indexb (to_list v) i = true.
   Proof.
     admit.
     (* depind v;cbn. easy.
     specialize (Fin.eqb_eq _ h i) as H'. split.
     intros H''. hnf in H''. inversion H''. destruct Fin.eqb;cbn.
     +split. 2:easy. intros H' . intuition. hnf. intros [-> | ]%In_cons. easy.
     eapply IHv. all:eauto. *)
   Admitted.

   Lemma not_index_reflect_helper n m (v : Vector.t _ m) (P : Fin.t n -> Prop):
    (forall i : Fin.t n, not_index v i  -> P i)
    -> (forall i : Fin.t n, if not_indexb (to_list v) i then P i else True).
    intros H i. specialize (H i). setoid_rewrite not_index_reflect in H. destruct not_indexb;easy.
    Qed.  

    Ltac simpl_not_in_vector_one :=
      let moveCnstLeft :=
        let rec loop k n :=
          lazymatch n with
           S ?n => loop uconstr:(S k) n
          | _ => uconstr:(k + n)
          end
        in loop 0
        in
      once lazymatch goal with
      | [ H : forall i : Fin.t ?n, not_index ?vect i -> _ |- _ ] =>
      specialize (not_index_reflect_helper H);clear H;intros H;
      let n' := moveCnstLeft n in
      change n with n' in H at 1;
      let tmp := fresh "tmp" in
      apply splitAllFin in H as [tmp H];
      cbn beta in H;
      let helper i :=
        let H' := fresh H "_0" in
        assert (H':= tmp i);
        cbn in H';
        once lazymatch type of H' with
          | if (if Nat.eqb ?k ?k then false else true) then _ else True => clear H'
          | ?i = ?j => move H' at bottom;symmetry in H';subst i
        end
      in
      match type of tmp with 
        forall i : Fin.t ?n, _ => 
         do_n_times_fin n helper;clear tmp     
      end
        (*simpl_not_in_vector_loop H vect n; clear H*)
      end.
      Set Ltac Profiling.

      simpl_not_in_vector_one. Show Ltac Profile. Check k.
      About Fin.eqb.
      Set
      

Ltac simpl_not_in_vector := repeat simpl_not_in_vector_one.

    Ltac 



    Lemma all_vec_correct2 {X:Type} {n:nat} (P : Vector.t X n -> Prop):
    (forall xs, P xs) -> all_vec P.
    Proof.  
      revert P. induction n;cbn;intros. now apply Vector.case0. easy.
    Qed.    
    




    vector_destruct tmid9.





  Lemma all_not_index_start n m  (v : Vector.t _ m) (P : _ -> Prop):
    (forall (i:Fin.t n),not_index v i -> P i) -> (forall i,not_index v (Fin.R 0 i) -> P (Fin.R 0 i)).
   easy.
  Qed.

  Lemma all_not_index_S n m k' (v : Vector.t _ m) (P : _ -> Prop):
  (forall (i:Fin.t (S n)),not_index v (Fin.R k' i) -> P (Fin.R k' i))
  -> P (Fin.R k' Fin0) /\ (forall (i:Fin.t n),not_index v (Fin.R (S k') i) -> P (Fin.R (S k') i)).

    (not_index v (Fin.R k i) -> P i).
   easy.
  Qed.

  Lemma all_not_index_S :

  Fixpoint AllFin (n:nat) : (Fin.t n -> Prop) -> Prop :=
    match n with
       0 => fun _ => True
      | S n => fun P => P Fin0 /\ AllFin (fun x => P (Fin.FS x))
    end.
    
    Lemma AllFin_correct n (P: Fin.t n -> Prop): AllFin P <-> forall x, P x.
    Proof.
      induction n in P|-*;cbn.
      {split. 2:easy. intros ? i. easy. }
      rewrite IHn. split. 2:easy.
      intros [] i. now eapply Fin.caseS'.
    Qed.

  Ltac decomposeAllFin H t :=
    is_var H;
    apply (proj2 (AllFin_correct _)) in H;
    cbn [AllFin] in H;
    repeat (let H' := fresh H in pose proof (H':= proj1 H);t H';simple apply proj2 in H );
    once lazymatch type of H with
       True => idtac
    | _ => setoid_rewrite -> (AllFin_correct) in H
    end.

    exfalso. clear - H23.


    Set Ltac Profiling. Search Fin.t "-".
    Ltac simpl_not_in_vector_one':=
      let helper H' := 
      is_var H';
      cbn [Fin.eqb not_indexb] in H';
       once lazymatch type of H' with
        | false = true -> _=> clear H'
        | true = true -> _ => specialize (H' eq_refl)
      end
      in
    once lazymatch goal with
    | [ H : forall i : Fin.t ?n, not_index ?vect i -> _ |- _ ] =>
    specialize (not_index_reflect H);clear H;intro H;
    cbn [to_list] in H;
    decomposeAllFin H helper;
    once lazymatch type of H with
       True => clear H
    | _ => idtac
    end;
    try helper H
    end.

    
    simpl_not_in_vector_one'.  

    rewrite <- (AllFin_correct) in H23.

    Fixpoint notInVector i vect
    
    Ltac simpl_not_in_vector_step H vect n m' :=
  let H' := fresh H "_" in
  tryif vector_contains m' vect
  then idtac (* skip m' *)
  else pose proof (H m' ltac:(vector_not_in)) as H'.

Ltac simpl_not_in_vector_loop H:=
  match type of H with

  let H' := fresh H "_" in
  pose proof I as H';
  do_n_times_fin n ltac:(fun m' => simpl_not_in_vector_step H vect n m');
  clear H'.

Ltac simpl_not_in_vector_one :=
  once lazymatch goal with
  | [ H : forall i : Fin.t ?n, not_index ?vect i -> _ |- _ ] =>
    simpl_not_in_vector_loop H
  end.

Ltac simpl_not_in_vector := repeat simpl_not_in_vector_one.
    
    simpl_not_in_vector.

    destruct_tapes. TMSimp. 
    rewrite <- H2, <- H4, <- H6, <- H8, <- H10, <- H12, <- H14, <- H16 in H, H20, H21.
    all: try now inversion 1.
    modpon H15. simpl_surject.
    TMSimp.
  Admitted.

End main.

Lemma encL_inj l1 l2 :
  encL l1 = encL l2 -> l1 = l2.
Proof.
  induction l1 in l2 |- *; intros H.
  - destruct l2; cbn in *; congruence.
  - destruct l2; cbn in *; try congruence.
    inversion H. f_equal; eauto.
    destruct a, b; now inversion H1.
Qed.

Lemma L_computable_function {k} R :
  @L_computable k R -> functional R.
Proof.
  intros [s Hs] v m1 m2 H1 H2.
  eapply Hs in H1. eapply Hs in H2.
  rewrite eval_iff in H1, H2.
  destruct H1 as [H1 H1'], H2 as [H2 H2'].
  eapply encL_inj, L_facts.unique_normal_forms; eauto.
  now rewrite <- H1, H2.
Qed.

Lemma Vector_hd_nth {k X} (v : Vector.t X (S k)) :
  Vector.hd v = v[@Fin0].
Proof.
  dependent destruct v. reflexivity.
Qed.

Theorem compiler_bool {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) :
  L_computable R -> TM_computable R.
Proof.
  intros H. 
  eapply TM_computable_rel'_spec.
  eapply L_computable_function; eauto.
  destruct H as [sim Hsim].
  exists n_main, Σ, sym_s, sym_b. split. eapply syms_diff. exists (M_main k sim). split.
  - eapply Realise_monotone. { eapply M_main_realise. }
    intros t [[] t'] H v ->.
    destruct (H v) as [m [Hm1 Hm2]]. reflexivity.
    exists m. split; eauto. rewrite <- Hm1.
    eapply Vector_hd_nth.
  - admit.
Admitted.
