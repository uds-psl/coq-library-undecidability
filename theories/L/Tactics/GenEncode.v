From Undecidability.L Require Import L Tactics.Computable Tactics.ComputableTactics Tactics.Extract.
From MetaCoq.Template Require Import All TemplateMonad.Core Ast.
Require Export String List.

Import MonadNotation.
Open Scope string_scope.

(** *** Generation of encoding functions *)

Fixpoint mkLApp (s : term) (L : list term) :=
  match L with
  | [] => s
  | t :: L => mkLApp (tApp (tConstruct (mkInd "L.L.term" 0) 1 []) [s; t]) L
  end.

Definition encode_arguments (B : term) (a i : nat) A_j :=
      A <- tmUnquoteTyped Type A_j ;;
      name <- (tmEval cbv (name_of A_j ++ "_term") >>=  Core.tmFreshName)  ;;
      E <- tmTryInfer name None (registered A);;
      t <- ret (@enc A E);;
      l <- tmQuote t;;
      ret (tApp l [tRel (a - i - 1) ]).

Definition mkMatch (t1 t2 d : Ast.term) (cases : nat -> list term -> Core.TemplateMonad term) :=
  hs_num <- tmGetOption (split_head_symbol t1) "no head symbol found";;
  let '(ind, Params) := hs_num in
  let params := List.length Params in
  L <- list_constructors ind >>= tmEval hnf ;; 
    body <- monad_map_i (fun i '(n, s, args) =>
                          l <- tmArgsOfConstructor ind i ;;
                          l' <- monad_map_i (insert_params FUEL Params) (skipn params l) ;;
                          t <- cases i l' ;; ret (args, t)) L ;; 
  ret (tCase (ind, params) (tLambda nAnon t1 t2) d
                                                body).

Definition tmMatchCorrect (A : Type) : Core.TemplateMonad Prop :=
  t <- (tmEval hnf A >>= tmQuote) ;; 
  hs_num <- tmGetOption (split_head_symbol t) "no inductive";;
  let '(ind, Params) := hs_num in
  num <- tmNumConstructors (inductive_mind ind) ;;
  x <- Core.tmFreshName "x" ;; 
  mtch <- mkMatch t (* argument type *) tTerm (* return type *) (tRel (2 * num))
           (fun i (* ctr index *) ctr_types (* ctr type *) => 
              args <- tmEval cbv (|ctr_types|);; 
              C <- monad_map_i (encode_arguments t args) ctr_types ;; 
              ret (stack (map (tLambda (nAnon)) ctr_types)
                               (((fun s => mkAppList s C) (tRel (args + 2 * (num - i) - 1)))))
           ) ;;
   E' <- Core.tmInferInstance None (registered A);;
   E <- tmGetOption E' "failed" ;;        
   t' <- ret (@enc A E);;
   l <- tmQuote t';;
   encn <- ret (tApp l [tRel (2*num) ]) ;;
   lhs <- ret (mkLApp encn ((fix f n := match n with 0 => [] | S n => tRel (2 * n + 1) :: f n end ) num)) ;;
   ter <- ret (tProd nAnon t (it (fun s : term => tProd nAnon tTerm (tProd nAnon (tApp (tConst "L.L.proc" []) [tRel 0]) s)) num ((tApp (tConst "L.L.redLe" []) [mkNat num; lhs; mtch]))));;
   ter <- tmEval cbv ter ;;
   tmUnquoteTyped Prop (fixNames ter).

Definition matchlem n A := (Core.tmBind (tmMatchCorrect A) (fun m => tmLemma n m ;; ret tt)).

Definition tmGenEncode (n : ident) (A : Type) :=
  e <- tmEncode n A;;
  e <- tmUnquoteTyped (encodable A) (tConst n []);;
  p <- Core.tmLemma (n ++ "_proc") (forall x : A, proc (@enc_f A e x)) ;;
  n2 <- tmEval cbv ((n ++ "_inj"));;
  i <- Core.tmLemma n2  (injective (@enc_f _ e)) ;;
  n3 <- tmEval cbv ("registered_" ++ n) ;;
  d <- Core.tmDefinition n3  (@mk_registered A e p i);;
  tmExistingInstance n3;;
  m <- tmMatchCorrect A;;
  n4 <- tmEval cbv (n ++ "_correct") ;;
  (Core.tmBind (tmMatchCorrect A) (fun m => tmLemma n4 m ;; ret tt)).

Definition tmGenEncode' (n : ident) (A : Type) :=
  e <- tmEncode n A;;
  e <- tmUnquoteTyped (encodable A) (tConst n []);;
  p <- Core.tmLemma (n ++ "_proc") (forall x : A, proc (@enc_f A e x)) ;;
  n2 <- tmEval cbv ((n ++ "_inj"));;
  i <- Core.tmLemma n2  (injective (@enc_f _ e)) ;;
  n3 <- tmEval cbv ("registered_" ++ n) ;;
  d <- Core.tmDefinition n3  (@mk_registered A e p i);;
  tmExistingInstance n3 ;;
  m <- tmMatchCorrect A ;; ret tt.

Global Obligation Tactic := try fold (injective (enc_f)); match goal with
                           | [ |- forall x : ?X, proc ?f ] => register_proc
                           | [ |- injective ?f ] => register_inj
                           | [ |- context [_ >(<= _) _] ] => extract match
                           end || Tactics.program_simpl.
