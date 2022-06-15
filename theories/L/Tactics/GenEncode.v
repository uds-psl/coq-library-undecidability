From Undecidability.Shared.Libs.PSL Require Import Base Bijection.
From Undecidability.L Require Import L Tactics.Computable Tactics.ComputableTactics Tactics.Extract.
From MetaCoq Require Import Template.All TemplateMonad.Core Template.Ast.
Require Import String List.
Export String.StringSyntax.

Import MCMonadNotation.
Local Open Scope string_scope.

(* *** Generation of encoding functions *)

Fixpoint mkLApp (s : term) (L : list term) :=
  match L with
  | [] => s
  | t :: L => mkLApp (tApp (tConstruct (mkInd term_kn 0) 1 []) [s; t]) L
  end.

Definition encode_arguments (B : term) (a i : nat) A_j :=
      A <- tmUnquoteTyped Type A_j ;;
      name <- (tmEval cbv (name_of A_j ++ "_term") >>=  Core.tmFreshName)  ;;
      E <- tmTryInfer name None (encodable A);;
      t <- ret (@enc A E);;
      l <- tmQuote t;;
      ret (tApp l [tRel (a - i - 1) ]).

Definition mkMatch (t1 t2 d : Ast.term) (pred : Ast.predicate term)  (cases : nat -> list term -> Core.TemplateMonad term) :=
  hs_num <- tmGetOption (split_head_symbol t1) "no head symbol found";;
  let '(ind, Params) := hs_num in
  let params := List.length Params in
  L <- list_constructors ind >>= tmEval hnf ;; 
  body <- monad_map_i (fun i '(n, s, args) =>
  l <- tmArgsOfConstructor ind i ;;
  l' <- monad_map_i (insert_params FUEL Params) (skipn params l) ;;
  t <- cases i l' ;; ret (mk_branch (context_to_bcontext args) t)) L ;; 
ret (tCase (mk_case_info ind params Relevant)
                        pred
                        d
                        body).

Definition L_facts_mp := MPfile ["L_facts"; "Util"; "L"; "Undecidability"].

Definition tmMatchCorrect (A : Type) : Core.TemplateMonad Prop :=
  t <- (tmEval hnf A >>= tmQuote) ;; 
  hs_num <- tmGetOption (split_head_symbol t) "no inductive";;
  let '(ind, Params) := hs_num in
  decl <- tmQuoteInductiveDecl (inductive_mind ind) ;;
  let '(mdecl,idecl) := decl in
  let params := firstn mdecl.(ind_npars) Params in
  num <- tmEval cbv (| ind_ctors idecl |) ;;
  x <- Core.tmFreshName "x" ;; 
  mtch <- mkMatch t (* argument type *) tTerm (* return type *) (tRel (2 * num))
           (mk_predicate Instance.empty params (context_to_bcontext (ind_predicate_context ind mdecl idecl)) tTerm)
           (fun i (* ctr index *) ctr_types (* ctr type *) => 
              args <- tmEval cbv (|ctr_types|);; 
              C <- monad_map_i (encode_arguments t args) ctr_types ;; 
              ret ( (* stack (map (tLambda (naAnon)) ctr_types) *)
                               (((fun s => mkAppList s C) (tRel (args + 2 * (num - i) - 1)))))
           ) ;;
   E' <- Core.tmInferInstance None (encodable A);;
   E <- tmGetMyOption E' "failed" ;;        
   t' <- ret (@enc A E);;
   l <- tmQuote t';;
   encn <- ret (tApp l [tRel (2*num) ]) ;;
   lhs <- ret (mkLApp encn ((fix f n := match n with 0 => [] | S n => tRel (2 * n + 1) :: f n end ) num)) ;;
   ter <- ret (tProd naAnon t (it (fun s : term => tProd naAnon tTerm (tProd naAnon (tApp (tConst (L_facts_mp, "proc") []) [tRel 0]) s)) num ((tApp (tConst (L_facts_mp, "redLe") []) [mkNat num; lhs; mtch]))));;
   ter <- tmEval cbv ter ;;
   tmUnquoteTyped Prop ter.

Definition matchlem n A := (Core.tmBind (tmMatchCorrect A) (fun m => tmLemma n m ;; ret tt)).

Definition tmGenEncode (n : ident) (A : Type) : TemplateMonad (encodable A) :=
  e <- tmEncode A;;
  modpath <- tmCurrentModPath tt ;;
  p <- Core.tmLemma (n ++ "_proc") (forall x : A, proc (e x)) ;;
  n3 <- tmEval cbv ("encodable_" ++ n) ;;
  d <- tmInstanceRed n3 None (mk_encodable p);;
  m <- tmMatchCorrect A;;
  n4 <- tmEval cbv (n ++ "_correct") ;;
  Core.tmBind (tmMatchCorrect A) (fun m' => tmLemma n4 m';;ret d).

Arguments tmGenEncode _%string _%type.

Definition tmGenEncodeInj (n : ident) (A : Type) : TemplateMonad unit :=
  d <- tmGenEncode n A;;
  n2 <- tmEval cbv ((n ++ "_inj"));;
  i <- Core.tmLemma n2  (@encInj A d);;
  n3 <- tmEval cbv ("encInj_" ++ n) ;;
  d <- tmInstanceRed n3 None i;;
  ret tt.

Arguments tmGenEncodeInj _%string _%type.


(*
Definition tmGenEncode' (n : ident) (A : Type) :=
  e <- tmEncode n A;;
  modpath <- tmCurrentModPath tt ;;
  e <- tmUnquoteTyped (encodable A) (tConst (modpath, n) []);;
  p <- Core.tmLemma (n ++ "_proc") (forall x : A, proc (@enc_f A e x)) ;;
  n2 <- tmEval cbv ((n ++ "_inj"));;
  i <- Core.tmLemma n2  (injective (@enc_f _ e)) ;;
  n3 <- tmEval cbv ("encodable_" ++ n) ;;
  d <- tmInstanceRed n3 None  (@mk_encodable A e p i);;
  m <- tmMatchCorrect A ;; ret tt. *)

(* TODO : use other methode instead, e.g. with typeclasses, as default obligation tactic is very fragile *)
Global Obligation Tactic := match goal with
                           | [ |- forall x : ?X, proc ?f ] => try register_proc
                           | [ |- encInj _ ] => unfold encInj;register_inj
                           | [ |- injective ?f ] => register_inj
                           | [ |- context [_ >(<= _) _] ] => extract match
                           end || Tactics.program_simpl.
