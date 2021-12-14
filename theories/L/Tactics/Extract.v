From Undecidability.L Require Import Util.L_facts Prelim.StringBase.
From MetaCoq Require Import Template.All Template.Checker.
Require Import Undecidability.Shared.Libs.PSL.Base. 
Require Import String Ascii.

Open Scope string_scope.
Import MCMonadNotation.

Unset Universe Minimization ToSet.

(* ** Extraction *)

(* Global definition of fuel for step-indexed computations *)
Notation FUEL := 1000.

(* Auxiliary functions *)
Definition string_of_int n :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | _ => "todo string_of_int"
  end.

(* it with acces to i *)
Section it_i.
  Variables (X: Type) (f: nat -> X -> X).

  Fixpoint it_i' (i : nat) (n : nat) (x : X) : X := 
    match n with
      | 0 => x
      | S n' => f i  (it_i' (S i) n' x)
    end.

  Definition it_i := it_i' 0.
End it_i.

(*  apply all functions in a list of functions from right to left *)
Definition stack {X : Type} (l : list (X -> X)) (x : X) := fold_right (fun f x => f x) x l.

(*  Auxiliary monadic functions *)

(* Get the head of a list *)
Definition hd {X : Type} (l : list X) : TemplateMonad X :=
  match l with
  | nil => tmFail "hd: empty list"
  | x :: _ => ret x
  end.

(* Get the type of a quoted term *)
Definition tmTypeOf (s : Ast.term) :=
  u <- tmUnquote s ;;
    tmEval hnf (my_projT1 u) >>= tmQuote.

(* Try to infer instance, otherwise make lemma *)
Definition tmTryInfer (n : ident) (red : option reductionStrategy) (A : Type) : TemplateMonad A :=
  r <- tmInferInstance red A ;;
    match r with
    | my_Some i => ret i
    | my_None =>
      A' <- match red with Some red => ret A | None => ret A end;;

         (* term <- tmQuote A';; *)
         (* tmEval cbv ("Did not find an instance for " ++ string_of_term term ++". You might want to register a instance for this.")  >>= tmFail *)
         (*Commented out because inside tactics, the error that tmLemmaRed is not allowed will hide the mor informative error massage above. *)
         tmPrint "Did not find an instance for ";;
         (tmPrint A');;
         (tmEval cbv ("open obligation " ++ n ++ " for it. You might want to register a instance before and rerun this.") >>= tmPrint);;
         tmLemma n A
    end.

(* Generate a name for a quoted term *)
Definition name_of (t : Ast.term) : ident :=
  match t with
    tConst (modp, n) _ => name_after_dot n
  | tConstruct (mkInd (modp, n) _) i _ => "cnstr_"  ++ name_after_dot n ++ string_of_int i
  | tInd (mkInd (modp, n) _) _ => "type_" ++ name_after_dot n
  | tVar i => "var_" ++ i
  | _ => "no_name" 
  end.

(* Fixpoint fixNames (t : term) := *)
(*   match t with *)
(*   | tRel i => tRel i *)
(*   | tEvar ev args => tEvar ev (List.map (fixNames) args) *)
(*   | tLambda na T M => tLambda na (fixNames T) (fixNames M) *)
(*   | tApp u v => tApp (fixNames u) (List.map (fixNames) v) *)
(*   | tProd na A B => tProd na (fixNames A) (fixNames B) *)
(*   | tCast C kind t => tCast (fixNames C) kind (fixNames t) *)
(*   | tLetIn na b t b' => tLetIn na (fixNames b) (fixNames t) (fixNames b') *)
(*   | tCase ind p C brs => *)
(*     let brs' := List.map (on_snd (fixNames)) brs in *)
(*     tCase ind (fixNames p) (fixNames C) brs' *)
(*   | tProj p C => tProj p (fixNames C) *)
(*   | tFix mfix idx => *)
(*     let mfix' := List.map (map_def (fixNames) (fixNames)) mfix in *)
(*     tFix mfix' idx *)
(*   | tCoFix mfix idx => *)
(*     let mfix' := List.map (map_def (fixNames) (fixNames)) mfix in *)
(*     tCoFix mfix' idx *)
(*   | tConst name u => tConst (name_after_dot name) u *)
(*   | tInd (mkInd name i) u => tInd (mkInd (name_after_dot name) i)  u *)
(*   | x => x *)
(*   end. *)

(* Check whether a list of quoted terms starts with a type *)
Fixpoint tmIsType (s : Ast.term) : TemplateMonad bool :=
  match s with
  | tInd _ _ => ret true
  | tConst n u => t <- tmTypeOf (tConst n u) ;; match t with tSort _ => ret true | _ => ret false end
  | tVar x => t <- tmTypeOf (tVar x) ;; match t with tSort _ => ret true | _ => ret false end
  | tApp h _ => tmIsType h
  | _ => ret false
  end.

(* Get the number of constructors for an inductive type *)
Definition tmNumConstructors (n : kername) : TemplateMonad nat :=
  i <- tmQuoteInductive n ;;
    match ind_bodies i with
      [ i ] => tmEval cbv (| ind_ctors i |)
    | _ => tmFail "Mutual inductive types are not supported"
    end.

(* Get all argument types for a type *)
Fixpoint argument_types (B : Ast.term) :=
  match B with
  | tProd _ A B => A :: argument_types B
  | _ => []
  end.

(* Split an inductive types applied to parameters into the naked inductive, the number of parameters and the list of parameters *)
Definition split_head_symbol A : option (inductive * list term) :=
  match A with
  | tApp (tInd ind u) R => ret (ind, R)
  | tInd ind u => ret (ind, [])
  | _ => None
  end.

(* Get the list of consturcors for an inductive type (name, quoted term, number of arguments) *)
Definition list_constructors (ind : inductive) : TemplateMonad (list (ident * term * context)) :=
  A <- tmQuoteInductive (inductive_mind ind) ;;
    match ind_bodies A with
    | [ B ] => tmReturn (map (fun cstr => (cstr.(cstr_name), cstr.(cstr_type), cstr.(cstr_args))) (ind_ctors B))
    | _ => tmFail "error: no mutual inductives supported"
    end.

(* determine whether two inductives are equal, based on their name *)
Definition eq_inductive (hs hs2 : inductive) :=
  match hs, hs2 with
  | mkInd k _, mkInd k2 _ => if kername_eq_dec k k2 then true else false
  end.

(* Get the argument types for a constructor (specified by inductive and index) *)
Definition tmArgsOfConstructor ind i :=
  A <- tmTypeOf (tConstruct ind i []) ;;
  ret (argument_types A).


(*  Classes for computable terms and (Scott-) encodable types *)

Class extracted {A : Type} (a : A) := int_ext : L.term.
Arguments int_ext {_} _ {_}.
#[export] Typeclasses Transparent extracted. (* This is crucial to use this inside monads  *)
#[export] Hint Extern 0 (extracted _) => progress (cbn [Common.my_projT1]): typeclass_instances. 

Class encodable (A : Type) := enc_f : A -> L.term.  

(* Construct quoted L terms and natural numbers *)

MetaCoq Quote Definition tTerm := L.term.

Definition term_mp := MPfile ["L"; "L"; "Undecidability"].
Definition term_kn := (term_mp, "term").

Definition mkLam x := tApp (tConstruct (mkInd term_kn 0) 2 []) [x].
Definition mkVar x := tApp (tConstruct (mkInd term_kn 0) 0 []) [x].
Definition mkApp x y := tApp (tConstruct (mkInd term_kn 0) 1 []) [x; y].

Definition mkAppList s B := fold_left (fun a b => mkApp a b) B s.

MetaCoq Quote Definition mkZero := 0.
MetaCoq Quote Definition mkSucc := S.

Fixpoint mkNat n := match n with
                   | 0 => mkZero
                   | S n => tApp mkSucc [mkNat n]
                   end.

(* *** Generation of Scott encodings *)

Fixpoint insert_params fuel Params i t :=
  let params := List.length Params in
  match fuel with 0 => tmFail "out of fuel in insert_params" | S fuel =>
  match t with
  | tRel n => (match nth_error Params (params + i - n - 1) with Some x => ret x | _ => ret (tRel n) (* tmFail "HERE" *) end)
  | tApp s R => s <- insert_params fuel Params i s ;;
                 R <- monad_map (insert_params fuel Params i) R;; 
                 ret (tApp s R)
  | _ => ret t
  end end.


Definition tmGetOption {X} (o : option X) (err : string) : TemplateMonad X :=
  match o with
  | Some x => ret x
  | None => tmFail err
  end.


Definition tmGetMyOption {X} (o : option_instance X) (err : string) : TemplateMonad X :=
  match o with
  | my_Some x => ret x
  | my_None => tmFail err
  end.

Definition naNamed n := {| binder_name := nNamed n; binder_relevance := Relevant |}.
Definition naAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

Fixpoint context_to_bcontext (ctx : context) : list aname :=
  match ctx with
  | [] => []
  | mkdecl a b c :: L => a :: context_to_bcontext L
  end.

Definition mkFixMatch (f x : ident) (t1 t2 : Ast.term) (pred : Ast.predicate term) (cases : nat -> list term -> TemplateMonad term) :=
  hs_num <- tmGetOption (split_head_symbol t1) "no head symbol found";;
  let '(ind, Params) := hs_num in
  let params := List.length Params in
  L <- list_constructors ind >>= tmEval hnf ;; 
  body <- monad_map_i (fun i '(n, s, args) =>
                          l <- tmArgsOfConstructor ind i ;;
                          l' <- monad_map_i (insert_params FUEL Params) (skipn params l) ;;
                          t <- cases i l' ;; ret (mk_branch (context_to_bcontext args) t)) L ;; 
  ret (Ast.tFix [BasicAst.mkdef 
                   Ast.term
                   (naNamed f)
                   (tProd naAnon t1 t2)
                   (tLambda (naNamed x) t1 (tCase (mk_case_info ind params Relevant)
                                                pred
                                                (tRel 0)
                                                body)) 0] 0).

#[global]
Existing Instance config.default_checker_flags.

Definition encode_arguments (B : term) (a i : nat) A_j :=
    if eq_term uGraph.init_graph B A_j
    then (* insert a recursive call *)
      ret (tApp (tRel (S a)) [tRel (a - i -1)])
    else (* insert a call to the appropriate encoding function *)
      A <- tmUnquoteTyped Type A_j ;;
      name <- (tmEval cbv (name_of A_j ++ "_term") >>=  tmFreshName)  ;;
      E <- tmTryInfer name None (encodable A);;
      t <- tmEval hnf (@enc_f A E);;
      l <- tmQuote t;;
      ret (tApp l [tRel (a - i - 1) ]).

Definition tmInstanceRed name red {X} (x:X) :=
  def' <- tmDefinitionRed name red x;;
  def <- tmQuote def';;
  match def with
    tConst name _ => tmExistingInstance (ConstRef name)
  | _ => tmFail "internal invariant violated : tmInstanceRed"
  end;;
  tmReturn def'.

Definition tmQuoteInductiveDecl (na : kername) : TemplateMonad (mutual_inductive_body * one_inductive_body) :=
  mdecl <- tmQuoteInductive na ;;
  match ind_bodies mdecl with
    [ idecl ] => tmReturn (mdecl, idecl)
  | _ => tmFail "Mutual inductive types are not supported"
  end.

Definition tmEncode (name : string) (A : Type) :=
  t <- (tmEval hnf A >>= tmQuote) ;; 
  hs_num <- tmGetOption (split_head_symbol t) "no inductive";;
  let '(ind, Params) := hs_num in
  decl <- tmQuoteInductiveDecl (inductive_mind ind) ;;
  let '(mdecl,idecl) := decl in
  num <- tmEval cbv (| ind_ctors idecl |) ;;
  let params := firstn mdecl.(ind_npars) Params in
  f <- tmFreshName "encode" ;;
  x <- tmFreshName "x" ;; 
  ter <- mkFixMatch f x t (* argument type *) tTerm (* return type *) (mk_predicate Instance.empty params (context_to_bcontext (ind_predicate_context ind mdecl idecl)) tTerm)
           (fun i (* ctr index *) ctr_types (* ctr type *) => 
              args <- tmEval cbv (|ctr_types|);; 
              C <- monad_map_i (encode_arguments t args) ctr_types ;; 
              ret ( (* stack (map (tLambda (naAnon)) ctr_types) *)
                               (it mkLam num ((fun s => mkAppList s C) (mkVar (mkNat (num - i - 1))))))
           ) ;;
  u <- tmUnquoteTyped (encodable A) ter;; 
 tmInstanceRed name None u;;
 tmEval hnf u.

(* **** Examples *)
(* Commented out for less printing while compiling *)

(* MetaCoq Run (tmEncode "unit_encode" unit >>= tmPrint). *)

(* MetaCoq Run (tmEncode "bool_encode" bool >>= tmPrint). *)

(* MetaCoq Run (tmEncode "nat_encode" nat >>= tmPrint). *)

(* MetaCoq Run (tmEncode "term_encode" L.term >>= tmPrint). *)

(* Inductive triple (X Y Z : Type) : Type := *)
(*   trip (x : X) (y : Y) (z : Z) : triple X Y Z. *)

(* Section encode. *)

(*   Variable A B C : Type. *)
(*   Context { encA : encodable A}. *)
(*   Context { encB : encodable B}. *)
(*   Context { encC : encodable C}. *)
    
(*   MetaCoq Run (tmEncode "prod_encode" (@prod A B) >>= tmPrint). *)

(*   MetaCoq Run (tmEncode "list_encode" (@list A) >>= tmPrint). *)

(*   MetaCoq Run (tmEncode "triple_encode" (@triple A B C) >>= tmPrint). *)

(* End encode. *)

(* *** Generation of constructors *)

Definition gen_constructor args num i  := 
  it lam args (it lam num (it_i (fun n s => L.app s #(n + num)) args (var (num - i - 1)))).

Definition extract_constr {A} (a : A) n (i : nat) (t : Ast.term) def' :=
  num <- tmNumConstructors n ;;
      r <- tmEval cbv (gen_constructor (|argument_types t|) num i : extracted a) ;;
      match def' with
      |  Some def =>  def2 <- tmFreshName def ;;
                     tmInstanceRed def2 None r;;tmReturn tt
      | None => tmReturn tt
      end;;
      ret r.

Definition tmExtractConstr' (def : option ident) {A : Type} (a : A) :=
  s <- (tmEval cbv a >>= tmQuote) ;;
  t <- (tmEval hnf A >>= tmQuote) ;;
     match s with
     | Ast.tApp (Ast.tConstruct (mkInd n _) i _) _ =>
         extract_constr a n i t def
     | Ast.tConstruct (mkInd n _) i _ =>
         extract_constr a n i t def
     | _ => tmFail "this is not a constructor"
     end.

Definition tmExtractConstr (def : ident) {A : Type} (a : A) :=
  tmExtractConstr' (Some def) a.

(* **** Examples *)
(* Commented out for less printing while compiling *)

(* Section Fix_X. *)

(*   Context {X : Set}. *)

(*   MetaCoq Run (tmExtractConstr "zero_term" 0 >>= tmPrint). *)

(*   MetaCoq Run (tmExtractConstr "S_term" S >>= tmPrint). *)
  
(*   MetaCoq Run (tmExtractConstr "nil_term" (@nil X) >>= tmPrint). *)
  
(*   MetaCoq Run (tmExtractConstr "cons_term" (@cons X) >>= tmPrint). *)
  
(* End Fix_X. *)

(* *** Extracting terms from Coq to L *)

Definition lift env := (fun n => match n with 0 => 0 | S n => S (env n) end).

Notation "↑ env" := (fun n => match n with 0 => 0 | S n => S (env n) end) (at level 10).
(*
Local Definition error {A} (a:A) := 1000.
Opaque error.

(*Get the free variables*)
Fixpoint freeVars (s:Ast.term) : list nat :=
  match s with
    tProd _ ty bd=>
    freeVars ty ++ (List.concat (map (fun x => match x with 0 => [] | S n => [n] end) (freeVars bd)))
  | tRel i => [i]
  | tApp hd args =>
    fold_left (fun l1 l2 =>List.app  l1 (freeVars l2)) args (freeVars hd)
  | tInd _ _ => []
  | tSort _ => []
  | tConstruct _ _ _ => []
  | tConst _ _ => []
  | _ => [error ("freeVars",s)] 
  end. 

Definition isClosed (s:Ast.term)
(*Get a term representing a type of form 'forall x1 ...xn, T' and returns the number of paramaters*)
Fixpoint dependentArgs (s:Ast.term) : nat :=
  match s with
    tProd _ ty bd=>
    let l := dependentArgs bd in
    match l with
      S n => S l
    | 0 => if existsb (fun x => x <=? 0) (freeVars bd) then 1 else 0
    end
  | _ => 0
  end.

Definition tmDependentArgs x:=
  match x with
    Ast.tConst _ _       => t <- tmTypeOf x;;tmEval cbn (dependentArgs t) >>= ret
  | Ast.tConstruct _ _ _ => t <- tmTypeOf x;;tmEval cbn (dependentArgs t) >>= ret
  | Ast.tRel _ => ret 0
  | Ast.tLambda _ _ _ => (*tmPrint ("tmDependentArgs currently assumes that abstractions on head position mean there are no parametric arguments");;*)ret 0
  | _ => (*tmPrint ("tmDependentArgs not supported");;*)ret 0
  end.
 *)

Fixpoint inferHead' (s:Ast.term) (revArg R: list Ast.term) : TemplateMonad (L.term * list Ast.term)  :=
  s'0 <- tmEval cbn (if forallb (fun _ => false) revArg then s else Ast.tApp s (rev revArg));;
  s' <- tmUnquote s'0;;
  s'' <- tmEval cbn (my_projT2 s');;
  res <- tmInferInstance None (extracted (A:=my_projT1 s') s'');;
  match res with
    my_Some s'' => ret (s'',R) 
  | my_None =>
    let doSplit := match R with
                    | [] => false
                    |  r :: R => if closedn 0 r then true else false 
                    end
    in
    match doSplit,R with
      true,r::R => inferHead' s (r::revArg) R
    | _,_ =>  let lhs := string_of_term s'0 in
             let rhs := string_of_list string_of_term R in
             tmMsg "More readable: initial segment:";;tmPrint s'';;tmMsg "With remainder:";;tmPrint R;;
             tmFail ("Could not extract in inferHead (moreReadable version in *coq*): could not infer any instance for initial segment of " ++lhs ++ " with further arguments "++ rhs)
    end
  end.
  
(* Tries to infer an extracted instance for all initial segments of the term, or to give *)
Definition inferHead (s:Ast.term) (R:list Ast.term) : TemplateMonad ((L.term + Ast.term) * list Ast.term)  :=
  match s with
    Ast.tConst _ _ |
  Ast.tConstruct _ _ _ =>
  res <- inferHead' s [] R;;
      let '(s',R):= res in
      ret (inl s',R)
  | _ => ret (inr s,R)
  end.

Fixpoint extract (env : nat -> nat) (s : Ast.term) (fuel : nat) : TemplateMonad L.term :=
  match fuel with 0 => tmFail "out of fuel" | S fuel =>
  match s with
    Ast.tRel n =>
    t <- tmEval cbv (var (env n));;
                        ret t
  | Ast.tLambda _ _ s =>
    t <- extract (↑ env) s fuel ;;
      ret (lam t)
  | Ast.tFix [BasicAst.mkdef nm ty s _] _ =>
    t <- extract (fun n => S (env n)) (Ast.tLambda nm ty s) fuel ;;
    ret (rho t)
  | Ast.tApp s R =>
    res <- inferHead s R;;
        let '(res,R') := res in
        (*tmPrint ("infHead:",res,R');;*)
    t <- (match res with
            inl s' => ret s'
          | inr s => extract env s fuel
          end);;
      monad_fold_left (fun t1 s2 => t2 <- extract env s2 fuel ;; ret (L.app t1 t2)) R' t
    (*else
      let (P, L) := (firstn params R,skipn params R)  in
      s' <- tmEval cbv (Ast.tApp s P);;
         (if closedn 0 s' then ret tt else tmPrint ("Can't extract ",s);;tmFail "The term contains variables as type parameters.");;
      a <- tmUnquote s' ;;
      a' <- tmEval cbn (my_projT2 a);;
      nm <- (tmEval cbv (String.append (name_of s) "_term") >>= tmFreshName) ;;
      i <- tmTryInfer nm (Some cbn) (extracted a') ;;
      let t := (@int_ext _ _ i) in
      monad_fold_left (fun t1 s2 => t2 <- extract env s2 fuel ;; ret (L.app t1 t2)) L t  *)                           
  | Ast.tConst n _ =>
    a <- tmUnquote s ;;
    a' <- tmEval cbn (my_projT2 a);;
    n <- (tmEval cbv (String.append (name_of s) "_term") >>= tmFreshName) ;;
    i <- tmTryInfer n (Some cbn) (extracted a') ;; (* TODO: Is hnf okay? *)
      ret (@int_ext _ _ i)

  | Ast.tConstruct (mkInd n _) _ _ =>
    a <- tmUnquote s ;;
    a' <- tmEval cbn (my_projT2 a);;
    nm <- (tmEval cbv (String.append (name_of s) "_term") >>= tmFreshName) ;;
    i <- tmTryInfer nm (Some cbn) (extracted a') ;;
      ret (@int_ext _ _ i)
  | Ast.tCase _ _ s cases =>
    t <- extract env s fuel ;;
      M <- monad_fold_left (fun t1 br => len <- tmEval cbv (List.length br.(bcontext)) ;; t2 <- extract (fun i => S (it lift (len) env i)) br.(bbody) fuel ;; t2' <- tmEval cbn (it lam len (lam t2)) ;; ret (L.app t1 t2')) cases t ;;
      ret (L.app M I)
  | Ast.tLetIn _ s1 _ s2 =>
    t1 <- extract env s1 fuel ;;
    t2 <- extract (↑ env) s2 fuel ;;
    ret( L.app (lam t2) t1)
     
  | Ast.tFix _ _ => tmFail "Mutual Fixpoints are not supported"                          
  | tVar _ =>     a <- tmUnquote s ;;
    a' <- tmEval cbn (my_projT2 a);;
    n <- (tmEval cbv (String.append (name_of s) "_term") >>= tmFreshName) ;;
    i <- tmTryInfer n (Some cbn) (extracted a') ;; 
      ret (@int_ext _ _ i)
  | tEvar _ _ =>   tmFail "tEvar is not supported"
  | tSort _ =>     tmFail "tSort is not supported"
  | tCast _ _ _ => tmFail "tCast is not supported"
  | tProd _ _ _ => tmFail "tProd is not supported"
  | tInd a _ =>  tmPrint a;;tmFail "tInd is not supported (probably there is a type not in prenex-normal form)" 
  | tProj _ _ =>   tmFail "tProj is not supported"
  | tCoFix _ _ =>  tmFail "tCoFix is not supported"
  | tInt _ =>  tmFail "tInt is not supported"
  | tFloat _ =>  tmFail "tFloat is not supported"
  end end.

Fixpoint head_of_const (t : term) :=
  match t with
  | tConst h _ => Some h
  | tApp s _ => head_of_const s
  | _ => None
  end.

Definition tmUnfoldTerm {A}(a:A) :=
  t <- tmQuote a;;
  match head_of_const t with
  | Some h => tmEval (unfold h) a >>=tmQuote
  | _ => ret t
  end.

Polymorphic Definition tmExtract (nm : option string) {A} (a : A) : TemplateMonad (extracted a) :=
  q <- tmUnfoldTerm a ;;
  t <- extract (fun x => x) q FUEL ;;
  match nm with
    Some nm => nm <- tmFreshName nm ;;
              @tmInstanceRed nm None (extracted a) t ;;
              ret t
  | None => ret t
  end.

Opaque extracted.

(* **** Examples *)
(* Commented out for less printing while compiling *)

(* Fixpoint ackermann n : nat -> nat := *)
(*   match n with *)
(*     0 => S *)
(*   | S n => fix ackermann_Sn m : nat := *)
(*             match m with *)
(*               0 => ackermann n 1 *)
(*             | S m => ackermann n (ackermann_Sn m) *)
(*             end *)
(*   end. *)

(* MetaCoq Run (tmExtractConstr "tm_zero" 0). *)
(* MetaCoq Run (tmExtractConstr "tm_succ" S). *)
(* (* MetaCoq Run (tmExtract (Some "tm_ack") ackermann >>= tmPrint). *) *)

(* (* Print tm_ack. *) *)

(* Require Import Init.Nat. *)
(* MetaCoq Run (tmExtract (Some "add_term") add ). *)
(* Print add_term. *)

(* MetaCoq Run (tmExtract (Some "mult_term") mult). *)

(* Section extract. *)

(*   Context { A B : Set }. *)
(*   Context { encB : encodable B }. *)

  
(*   MetaCoq Run (tmExtract (Some "map_term") (@map A B) >>= tmPrint). *)
(*   Print map_term. *)
  
(*   MetaCoq Run (tmExtract (Some "filter_term") (@filter A) >>= tmPrint). *)
(*   Print filter_term. *)
  
(* End extract. *)

Global Obligation Tactic := idtac.

#[export] Typeclasses Transparent encodable.
