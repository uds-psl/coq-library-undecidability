Require Import MetaCoq.Template.All Strings.Ascii.
From Undecidability.L.Tactics Require Import Lproc Computable Lsimpl Lbeta Lrewrite.
Require Export Ring Arith Lia.
Import L_Notations.

(* ** Tactics proving correctness *)
Module Intern.
  
Ltac visibleHead t :=
  match t with
    ?h _ => visibleHead h
  | _ => t
  end.

Ltac fold_encs :=
  match goal with
    x:_ |- _ =>
    revert x;fold_encs;intros x;
    let H := fresh "H" in
    try (assert (H:@enc _ _ x= @enc _ _ x) by reflexivity;
         try (unfold enc in H at 1; cbn in H;rewrite !H);clear H)
  | _ => idtac
  end.


Ltac recRem P:=
  match goal with
  | |- context[rho ?s] =>
    let rP := fresh "rP" in
    set (rP:=s);
    assert (proc rP);[unfold rP;solve [Lproc]|
                      set (P := rho rP);
                      assert (proc P);[unfold P;solve [Lproc]|]]
  end.

Ltac recStepInit P:=
   once lazymatch eval lazy [P] in P with
   | rho ?rP =>
     once lazymatch goal with
     | |- eval _ _ =>
       let rec loop := 
           once lazymatch goal with
           | |- ARS.star step (app P _) _ =>unfold P;apply rho_correct;now Lproc
           | |- ARS.star step (app _ _) _ => eapply star_step_app_proper;[loop|reflexivity]
           end
       in
       eapply eval_helper;[loop|fold P; unfold rP]
     end
   end.


Ltac recStepNew P := recStepInit P.


Ltac destructRefine :=
  once lazymatch goal with
    |- ?R ?s _ =>
    match s with
    | context C [match ?x with _ => _ end]=>
      let t := type of x in
      refine (_:R _ ((fun y:t => ltac:(destruct y)) x));
      (* refine index if applicable*)
      once lazymatch goal with
        |- (?R' ?i ?s1 ?s2) => tryif is_evar i then
          refine (_:R' ((fun (y:t) (*(_ : x=y)*) => ltac:(destruct y)) x ) s1 s2)
        else idtac
      | _ => idtac
      end;
      once lazymatch goal with
       | |- ?R2 ?i ?s ?t =>
         let i':= eval cbn zeta in i in
             refine (_:R2 i' s t) + match goal with |- ?G => let G' := constr:(R2 i' s t) in idtac "could not refine" G "with" G' end
       | _ => idtac
      end;
      let eq := fresh "eq" in destruct x eqn:eq
    end
  end.

Ltac shelveIfUnsolved msg:= first[let n:= numgoals in guard n=0|
                                  match goal with
                                    |- ?G => idtac "Could not solve some subgoal("msg"):";idtac G;shelve
                                  end].

Ltac ugly_fix_fix IH n :=
  (* we must destruct to allow the fix to reduce...*)
  once lazymatch eval cbn in n with
    0 => fix IH 1
  | 1 => fix IH 4
  | 2 => fix IH 7
  | 3 => fix IH 10
  | _ => let m := eval cbn in (1+3*n) in
            fail 1000 "please add '| "n" => fix IH"m"'" " in the definition of Ltac-tactic ugly_fix_fix!"
  end.

(* a non-recursive step*)
Ltac cstep' extractSimp:=
  let x := fresh "x" in
  once lazymatch goal with
  | |- computes _ _ (match ?x with _ => _ end)=>
    let eq := fresh "eq" in destruct x eqn:eq
  | |- computes (TyArr ?tt1 ?tt2) ?f ?intF=>
    let fRep := constr:(ltac:(quote_term f (fun x => exact x))) in
    once lazymatch fRep with
      (* a potentially recursive step *)
      Ast.tFix (_::_::_) => fail 1000 "mutual recursion not supported"
    | Ast.tFix [BasicAst.mkdef _ _ _(*<-dtype*) _(*<-dbody*) ?recArg(*<-recArg*)] 0 =>
      (let P := fresh "P" in
      recRem P;
      eapply computesExpStart;[solve [Lproc]|];
      let n:= (eval cbn in (S recArg)) in
      let rec step n:=
          (once lazymatch n with
           |  S ?n =>
              eexists;
              eapply computesExpStep;[try recStep P;extractSimp;shelveIfUnsolved "pos5"|Lproc;shelveIfUnsolved "pos6"|];
              (*simple notypeclasses refine (_:computes (_ ~> _) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*)
              let x := fresh "x" in  
              let xInt := fresh x "Int" in
              let xInts := fresh x "Ints" in
              intros x xInt xInts;
              change xInt with (@ext _ _ x (Build_computable xInts));
              once lazymatch type of xInts with
                computes (@TyB _ ?reg) _ _ =>
                rewrite (ext_is_enc (Build_computable xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
              | computes (TyArr _ _) _ _ => idtac
              end;
              step n;
              revert x xInt xInts
           | 0 => idtac
           end) in
      step n;
        let IH := fresh "IH" P in
        ugly_fix_fix IH recArg;
          let rec loop n := (* destruct the struct-recursive argument*)
              once lazymatch n with
                0 => intros [] ? ?
              | S ?n' => intros ? ? ?;loop n'
              end in
          loop recArg;
          eexists;
          (split;[try recStepNew P;extractSimp;shelveIfUnsolved "pos7"|]))

    (* a non-recursive function *)
    | _=>
      let xInt := fresh x "Int" in
      let xNorm := fresh x "Norm" in
      let xInts := fresh x "Ints" in
      let vProc := fresh "vProc" in
      (*simple notypeclasses refine (_:computes (tt1 ~> tt2) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*)
      eapply computesTyArr;[try Lproc;shelveIfUnsolved "pos1"|idtac];
      intros x xInt xInts;
      change xInt with (@ext _ _ x (Build_computable xInts));
      once lazymatch tt1 with
        TyB _ => rewrite (ext_is_enc (Build_computable xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
      | _ => idtac
      end;
      eexists;split;[extractSimp;shelveIfUnsolved "pos2" | intros vProc]
    end

  | |- computes (TyB _) _ ?t=> has_no_evar t;apply computesTyB

  | |- computes _ _ (@ext _ _)=> apply extCorrect

  end.

Tactic Notation "progress'" tactic(t) :=
  once lazymatch goal with
    | |- ?R ?s _ =>idtac "now";print_goal;
    t tt;idtac"then";print_goal;
    once lazymatch goal with
      |- R s _ => fail "noprogress"
    | |- _ => idtac
    end
  end.

Ltac extractCorrectCrush :=
  idtac;
   try Lsimpl;try Lreflexivity;
   try repeat' (repeat' Intern.destructRefine;Lsimpl;try Lreflexivity);
  try Lreflexivity.

Ltac extractSimple := 
  lazymatch goal with
    |- eval _ _ => extractCorrectCrush
  | |- ?G => idtac "cstep found unexpected" G 
  end;try (idtac;[idtac "could not simplify some occuring term, shelved instead"];shelve).

Ltac cstep := cstep' extractSimple.

Ltac computable_match:=
  intros;
  once lazymatch goal with
  | |- ?R ?lhs ?rhs =>
    once lazymatch lhs with 
    | context C [@enc _ ?reg ?x] =>
      induction x;
      let encf := (eval hnf in (@enc _ reg)) in
      change (@enc _ reg) with encf;
      cbn -[enc];
      repeat change encf with (@enc _ reg);
      fold_encs;
      once lazymatch goal with
      | |- _ >(<= _ ) _ => Lreduce;try Lreflexivity
      | |- _ >(_) _ => repeat progress Lbeta;try Lreflexivity
      | |- _ >* _ => Lreduce;try Lreflexivity (* test *)
      | |- eval _ _ => Lreduce;try Lreflexivity (* test *) 
      (*| |- _ >* _  => repeat Lsimpl';try reflexivity'
      | |- eval _ _  => repeat Lsimpl';try reflexivity'*)
      | |- _ == _  => repeat Lsimpl';try reflexivity'
      end
    end
  end.

Ltac infer_instances :=
  repeat match goal with
         | [ |- context [ int_ext ?t ] ] => first [change (int_ext t) with (ext t) | fail 3 "Could not fold int-instance for " t]
         end.

Ltac computable_prepare t :=
  let h := visibleHead t in
  tryif is_const h then unfold h else idtac.

Ltac computable_using_noProof Lter:=
  once lazymatch goal with
  | [ |- computable ?t ] =>
    eexists Lter;unfold Lter;try clear Lter;
    let t' := eval hnf in t in
        let h := visibleHead t' in
        try unfold h;computable_prepare t;infer_instances
  end.


Ltac extractAs s :=
  once lazymatch goal with
  | [ H : @extracted _ |- _ ] => idtac "WARNING: extraction is buggy if used while a term of type 'extracted _' is in Context"
  | [ |- computable ?t ] =>
    (run_template_program (tmExtract None t)
                         (fun e =>  pose (s:= ( e : extracted t))))
  end.


Ltac extractThis t s :=
    (run_template_program (tmExtract None t)
                         (fun e =>  pose (s:= ( e : extracted t)))).

End Intern.

Import Intern.

Ltac register_inj := 
  abstract (intros x; induction x; let y := fresh "y" in destruct y;simpl; intros eq;
    try (injection eq || discriminate eq);intros;f_equal;auto;try apply inj_enc;try easy).

Ltac register_proc :=
  solve [
  let x := fresh "x" in
  (((intros x;induction x || intros *);
    cbn; fold_encs;Lproc
                        ))].

Ltac register encf :=   refine (@mk_encodable _ encf _);[
                          (((let x := fresh "x" in induction x || intros);(let f := Intern.visibleHead encf in unfold f;cbn [f]);
                            Lproc
                        ))].


Tactic Notation "computable" "using" open_constr(Lter) :=
  computable_using_noProof Lter;repeat cstep.

Tactic Notation "computable" "instead" open_constr(t) :=
  let s := fresh "s" in
  extractThis t s; computable using s.
      
Tactic Notation "computable" "infer" :=
  once lazymatch goal with
  | [ |- computable ?t ] =>
    let e := constr:(int_ext t) in let e' := eval unfold int_ext in e in computable using e'
  end.

Tactic Notation "extract" :=
  unshelve
    let term := fresh "used_term" in
    extractAs term;computable using term.


Tactic Notation "extract" "constructor":=
  let term := fresh "used_term" in
        once lazymatch goal with
        | [ |- computable ?t ] =>
          run_template_program (tmExtractConstr' None t)
                                 (fun e =>  pose (term:= ( e : extracted t)); computable using term)
   end.

Tactic Notation "extract" "match" := computable_match.

Lemma cast_computable X Y `{encodable Y} (cast : X -> Y) :
  let _ := registerAs cast in
  computable cast.
Proof.
  cbn.
  pose (t:=lam 0).
  computable using t.
Qed.

Ltac computable_casted_result :=
  match goal with
    |- @computable _ _ _ => 
    simple notypeclasses refine (cast_registeredAs _ _);
    [ | | |
      cbn - [registerAs];reflexivity| ];
    cbn
  end.
