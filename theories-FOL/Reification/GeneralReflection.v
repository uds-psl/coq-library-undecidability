From FOL Require Import FullSyntax.
From MetaCoq.Template Require Import utils All Pretty Checker.
Require Import List String Lia.

(* Both metacoq and FOL have terms. *)
Notation term := Core.term.
(* * Reification
      Please read the PDF file giving a detailed description.
      
      We are given a Coq term and try to find a reification of it in the syntax of a specific kind of first-order theory. *)
Section FailureMonad.
  (* ** FailureMonad
      Since our function is partial, and we want to give helpful error messages to the User, we use this monad, which represents either success or failure, along with an error message
  *)
  Inductive FailureMonad (A:Type) : Type := ret : A -> FailureMonad A | fail : string -> FailureMonad A.
  Arguments ret {_} _.
  Arguments fail {_} _.
  Definition bind {A B : Type} (k:FailureMonad A) (f:A -> FailureMonad B) := match k return FailureMonad B with fail x => fail x | ret k => f k end.
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) (at level 100, c2 at level 100, c1 at next level).
  (* "Converts" from our monad to the TemplateMonad of MetaCoq. This is used to pass error messages back to the user *)
  Definition f2t {T:Type} (a:FailureMonad T) : TemplateMonad T := match a with ret k => monad_utils.ret k | fail s => tmFail s end.
  (* Structurally recursive definition of a monadic map *)
  Fixpoint flatten_monad {A:Type} (l:list (FailureMonad A)) : FailureMonad (list A) := match l with nil => ret nil | x::xr => (xm <- x;; (xrm <- flatten_monad xr;; ret (xm::xrm))) end.
  Definition map_monad {A B:Type} (f:A -> FailureMonad B) (l:list A) : FailureMonad (list B) := flatten_monad (map f l).
  (* If the first monad fails, use the second. Used to cascade failure handling *)
  Definition orelse {A:Type} (F1 F2 :FailureMonad A) := match F1 with fail _ => F2 | _ => F1 end.
  Definition fail_fmap {A B : Type} (f : A -> B) (a : FailureMonad A) : FailureMonad B := aa <- a ;; ret (f aa).
  Definition fail_fmap' {A B : Type} (a : FailureMonad A) (f : A -> B) : FailureMonad B := fail_fmap f a.
End FailureMonad.

Arguments ret {_} _.
Arguments fail {_} _.
Arguments orelse {_} _ _.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) (at level 100, c2 at level 100, c1 at next level).
Notation "x >>= f" := (bind x f) (at level 100).
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Section MetaCoqUtils.
  (* ** MetaCoqUtils
         Here, we define various useful functions for working with MetaCoq terms *)
  (*+ Working with quoted vectors *)
  Notation vectorCons x T n xr := 
  (tApp
   (tConstruct
      {|
      inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t");
      inductive_ind := 0 |} 1 nil)
   ([T; x; n; xr])).
  Notation vectorNil T :=
  (tApp
   (tConstruct
      {|
      inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t");
      inductive_ind := 0 |} 0 nil) ([T])).
  (* Unquotes a vector (into a list) *)
  Fixpoint recoverVector (f : Ast.term) {struct f}: FailureMonad (list Ast.term) := let ffail := fail "not a vector application" in match f with
    vectorNil _ => ret nil
  | vectorCons x _ _ xr => xrl <- recoverVector xr;;ret (x::xrl)
  | _ => ffail
  end.

  (* *** General utils for quoted terms *)
  (* Remove the n first elements from a list *)
  Existing Instance config.default_checker_flags.
  Fixpoint popNElements (l : list Ast.term) (n:nat) : option (list Ast.term) := match (l,n) with
    (a,0) => Some a
  | (x::xr, S n) => popNElements xr n
  | _ => None end.
  (* If ls is a valid prefix of l, return the corresponding "suffix" (the remaining elements of l). Otherwise, return None *)
  Fixpoint popListStart (l : list Ast.term) (ls : list Ast.term) : option (list Ast.term) := match (l,ls) with
    (a,nil)=> Some a
  | (lx::lxr, lsx::lsxr) => if eq_term init_graph lx lsx then popListStart lxr lsxr else None
  | _ => None end.
  MetaCoq Quote Definition qNatZero := 0.
  MetaCoq Quote Definition qNatSucc := S.
  MetaCoq Quote Definition qeq_refl := (@eq_refl).
  (* Given n, yield a MetaCoq Ast.term representation of n *)
  Fixpoint quoteNumber (n:nat) : Ast.term:= match n with 0 => qNatZero | S n => tApp qNatSucc ([quoteNumber n]) end.
  (* Increases the indices of all tRel in t by amnt, assuming they are already larger than minn. If minn = 0, this increases all "free" tRel reference indices *)
  Definition addRelIndex (minn:nat) (amnt:nat) (t:Ast.term) : Ast.term := Ast.lift amnt minn t. 

  (* Helper functions, adapted from Ast.subst (for lowerRelIndex) and its helpers *)
  Definition map_predicate_fail {term term' : Type} (uf : Instance.t -> Instance.t) (paramf preturnf : term -> FailureMonad term') (p : predicate term) : FailureMonad (predicate term') :=
    pparams' <- map_monad paramf (pparams p) ;;
    preturn' <- preturnf (preturn p) ;;
    ret {| puinst := uf (puinst p); pparams := pparams'; pcontext := pcontext p; preturn := preturn' |}.
  Definition map_branch_fail {term term' : Type} (bbodyf : term -> FailureMonad term') (b : branch term) := 
    bbody' <- bbodyf (bbody b) ;;
    ret {| bcontext := bcontext b; bbody := bbody' |}.
  Definition map_def_fail {A B : Type} (tyf bodyf : A -> FailureMonad B) (d : def A)  := 
    ty' <- tyf (dtype d);;
    body' <- bodyf (dbody d);;
    ret {| dname := dname d; dtype := ty'; dbody := body' ; rarg := rarg d |}.
  (* monadic single-term substitution. *)
  Fixpoint subst (s : FailureMonad Ast.term) (k:nat) (u:Ast.term) :=
    match u with
    | tRel n =>
      if k <=? n then ss <- s;; ret (addRelIndex 0 k ss)
      else ret (tRel n)
    | tEvar ev args => fail_fmap (tEvar ev) (map_monad (subst s k) args)
    | tLambda na T M => (subst s k T) >>= (fun T => fail_fmap (tLambda na T) (subst s (S k) M))
    | tApp u v => (subst s k u) >>= (fun u => fail_fmap (mkApps u) (map_monad (subst s k) v))
    | tProd na A B => (subst s k A) >>= (fun u => fail_fmap (tProd na u) (subst s (S k) B))
    | tCast c kind ty => (subst s k c) >>= (fun c => fail_fmap (tCast c kind) (subst s k ty))
    | tLetIn na b ty b' => b <- (subst s k b);; ty <- (subst s k ty) ;; b' <- (subst s (S k) b') ;; ret (tLetIn na b ty b')
    | tCase ind p c brs =>
      let k' := List.length (pcontext p) + k in
      p' <- map_predicate_fail id (subst s k) (subst s k') p ;;
      brs' <- map_monad (fun b => map_branch_fail (subst s (#|b.(bcontext)| + k)) b) brs ;;
      c' <- (subst s k c) ;;
      ret (tCase ind p' c' brs')
    | tProj p c => fail_fmap (tProj p) (subst s k c)
    | tFix mfix idx =>
      let k' := List.length mfix + k in
      mfix' <- map_monad (map_def_fail (subst s k) (subst s k')) mfix ;;
      ret (tFix mfix' idx)
    | tCoFix mfix idx =>
      let k' := List.length mfix + k in
      mfix' <- map_monad (map_def_fail (subst s k) (subst s k')) mfix ;;
      ret (tCoFix mfix' idx)
    | x => ret x
    end.

  Definition lowerRelIndex (minn:nat) (tv:FailureMonad Ast.term) (t:Ast.term) : FailureMonad Ast.term := subst tv minn t.
End MetaCoqUtils.

Section AbstractReflectionDefinitions.
  (* ** AbstractReflectionDefinitions
         Here, we define basic terms and types used when reifying *)
  (* Type of term reification helper, which is given to extension points / base connective reifier.
      The arguments are:
      - tct:Ast.term -- the current instance of the tarski_reflector, quoted
      - qff:Ast.term -- the instance of falsity_flag
      - t:Ast.term -- the actual term to be reified
      - envTerm:Ast.term -- the env we are reifying into, quoted
      - env: -- a helper, which gives the env index for Coq terms
      - returning a pair of the reified term and a proof that it is correct, both quoted *)
  Definition helperTermReifierType := (Ast.term -> Ast.term -> Ast.term -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad (prod Ast.term Ast.term)).
  (* The same, but used during the env constructing phase. The only arg is the term itself *)
  Definition helperTermVarsType := (Ast.term -> FailureMonad (list Ast.term)).
  (* Similar, but this helper is used to reify terms, not forms. Args:
      - qff:Ast.term -- as above
      - frees:nat -- when reifying a nary predicate, this is n.
      - t:Ast.term -- the actual term/form to be reified
      - envTerm -- as above
      - env -- as above
      - returning again a apair of reified term and proof *)
  Definition helperFormReifierType := (Ast.term -> Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad (prod Ast.term Ast.term)).
  Definition helperFormVarsType := (Ast.term->nat->FailureMonad (list Ast.term)).
  (* A base connective is an inductive in Coq.Init.Logic, like and. They are common and have their own subsystem. Arguments:
      - tct, qff:Ast.term -- as above
      - lst:list Ast.term -- for e.g. (and X Y), this list contains [X;Y].
      - fuel:nat -- fuel (when 0, we stop)
      - envTerm
      - env
      - a helper to recursively reify forms
      - a helper to recursively reify terms
      - return again a a pair of term and proof *)
  Definition baseConnectiveReifier := Ast.term -> Ast.term -> list Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> helperFormReifierType -> helperTermReifierType -> FailureMonad (prod Ast.term Ast.term).
  Definition baseConnectiveVars := list Ast.term -> nat -> Ast.term -> helperFormVarsType -> helperTermVarsType -> FailureMonad (list Ast.term).
  (* Extension point for term reification. Args are:
      - tct:Ast.term
      - qff:Ast.term -- the instance of falsity_flag
      - fuel:nat (also for var finder)
      - t:term (also for var finder) -- the actual term
      - envTerm
      - env
      - recursion helper (also for var finder)
      - returning the usual *)
  Definition termFinderVars := nat -> Ast.term -> helperTermVarsType -> FailureMonad (list Ast.term).
  Definition termFinderReifier := Ast.term -> Ast.term -> nat -> Ast.term -> Ast.term -> (Ast.term -> FailureMonad nat) 
                                  -> helperTermReifierType -> FailureMonad (prod Ast.term Ast.term).
  (* Extension point for form reification. Args are:
      - tct:Ast.term
      - qff:Ast.term -- the instance of falsity_flag
      - fuel:nat (also for var finder)
      - t:term (also for var finder) -- the actual term
      - frees
      - envTerm
      - env
      - recursion helper for forms (also for var finder)
      - recursion helper for terms (also for var finder)
      - returning the usual *)
  Definition propFinderVars := Ast.term -> nat -> Ast.term -> nat -> helperFormVarsType -> helperTermVarsType -> (FailureMonad (list Ast.term)).
  Definition propFinderReifier := Ast.term -> Ast.term -> nat -> Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> helperFormReifierType -> helperTermReifierType -> FailureMonad (prod Ast.term Ast.term).

  (* When running in no proof mode, extension points still expect proofs. We give this dummy term. If the extension point only uses this to build further proofs, the whole term is discarded in the end *)
  Definition noProofDummy := tVar "NoProofGivenBecauseWeAreInNoProofMode".
  (* An instance of this class is required for the reifier to work. From it the basic reification building blocks are derived *)
  Class tarski_reflector := {
    fs : funcs_signature; 
    ps : preds_signature; (* ps and fs give the syntax *)
    D  : Type;
    I  : @interp fs ps D; (* D and I give our model *)
    emptyEnv : nat -> D;  (* We need an "empty" env that returns some default value for our types *)
    isD : Ast.term -> bool;  (* Returns true iff the given term references D used above *)
  }.
  (* Extension point to extend the libary to more syntactic constructs *)
  Class tarski_reflector_extensions (t:tarski_reflector) := {
    (* for reifying instances of inductive types Coq.Init.Logic.* applied to arguments. Mostly used for reifying eq *)
    baseLogicConnHelper : option (string -> baseConnectiveReifier); 
    baseLogicVarHelper : option (string -> baseConnectiveVars);
    (* for reifying all terms that we fail to reify *)
    termReifierVarHelper : option termFinderVars;
    termReifierReifyHelper : option termFinderReifier;
    (* for reifying all forms that we fail to reify *)
    formReifierVarHelper : option propFinderVars;
    formReifierReifyHelper : option propFinderReifier
  }.
  (* Used if no instance of the above extension class can be found. Low priority *)
  Definition defaultExtensions tr : tarski_reflector_extensions tr := Build_tarski_reflector_extensions tr None None None None None None.
  (* Useful builder to build the main tarski_reflector class *)
  Definition buildDefaultTarski {fs:funcs_signature} {ps:preds_signature} {D:Type} {I:@interp fs ps D} (point:D) (isD:Ast.term -> bool)
     := @Build_tarski_reflector fs ps D I (fun n:nat => point) isD.

  Fixpoint anyVariableOf (l:list ident) (t:Ast.term) := match l with nil => false | lx::lr =>
        if @Checker.eq_term config.default_checker_flags init_graph t (tVar lx) then true else anyVariableOf lr t end.

  Context {tr : tarski_reflector}.
  Context {ff : falsity_flag}.
  (* These types are used to define representability. A n-ary formula is representable if there is a syntactic formula and an environment that you can plug the relevant values into that is equivalent *)
  Fixpoint naryProp (n:nat) : Type := match n with 0 => Prop | S nn => D -> naryProp nn end.
  Fixpoint representsP {n:nat} phi rho : (forall (P:naryProp n), Prop) := match n return (forall (P:naryProp n), Prop) with
       0  => (fun (P:Prop) => P <-> @sat fs ps D I ff rho phi)
    | S n => (fun (P:D -> naryProp n) => forall d, @representsP n phi (d.:rho) (P d)) end.
  Definition representableP (n:nat) (P : naryProp n) := {phi&{rho | representsP phi rho P}}.
  Definition representsF (d:D) trm rho := @eval fs ps D I rho trm = d.
  Definition representableF (d:D) := exists trm rho, representsF d trm rho.


  (* Functions that allow us to construct syntactic connective applications without building vectors in MetaCoq *)
  Fixpoint naryGFunc (n:nat) (A R : Type) := match n with 0 => R | S n => A -> @naryGFunc n A R end.
  Fixpoint takeMultiple {n : nat} (X Y:Type)  : (Vector.t X n -> Y) -> @naryGFunc n X Y := 
     match n as nn return (Vector.t X nn -> Y) -> @naryGFunc nn X Y
             with 0 => fun R => R (Vector.nil X) 
              | S n => fun R v => @takeMultiple n X Y (fun vr => R (Vector.cons X v n vr)) end.

  Definition constructTerm (k:@syms (@fs tr)) := @takeMultiple (ar_syms k) term term (func k).
  Definition constructForm (k:(@preds (@ps tr))) := @takeMultiple (@ar_preds (@ps tr) k) (@term (@fs tr)) form (atom k).

  Fixpoint nary3GFunc (n:nat) (A B A' B':Type) (C:A -> B -> Type) (C':A'->B'->Type) : (Vector.t A n -> A') -> (Vector.t B n -> B') -> Type
                      := match n with 0 => fun mA mB => C' (mA (Vector.nil A)) (mB (Vector.nil B))
                                  | S n => fun mA mB => forall (a:A) (b:B), C a b -> @nary3GFunc n A B A' B' C C' (fun v => mA (Vector.cons A a n v)) (fun v => mB (Vector.cons B b n v)) end.

  Definition mergeTermBase (c:@syms (@fs tr)) : Type := 
  forall (rho:nat -> D), @nary3GFunc (ar_syms c) term D term D 
                                     (fun t d => representsF d t rho) (fun t d => representsF d t rho) 
                                     (func c) (@i_func fs ps D I c).
  (* Hack to get these to use the proper type class instance *)
  Notation term := (@Core.term (@fs tr)).
  Notation form := (@Core.form (@fs tr) (@ps tr) full_operators ff).
  Notation syms := (@Core.syms (@fs tr)).
  Notation preds := (@Core.preds (@ps tr)).
  Definition mergeTermProtoType (rho:nat -> D) (n:nat) (fZ:Vector.t term n -> term) (ifZ : Vector.t D n -> D) := 
         (forall v : Vector.t term n, @eval fs ps D I rho (fZ v) = ifZ (Vector.map (@eval fs ps D I rho) v))  
         -> @nary3GFunc n term D term D (fun t d => representsF d t rho) (fun t d => representsF d t rho) fZ ifZ.
  Definition mergeTermProto (rho:nat -> D) (n:nat) (fZ:Vector.t term n -> term) (ifZ : Vector.t D n -> D) : @mergeTermProtoType rho n fZ ifZ.
  Proof.
  intros H. induction n as [|n IH].
  * cbn. unfold representsF. rewrite H. cbn. easy.
  * cbn. intros t d r. apply IH. cbn. intros v. specialize (H (Vector.cons t v)). unfold representsF in r. rewrite H. cbn. now rewrite r.
  Defined.
  Definition mergeTerm (c:syms) : mergeTermBase c.
  Proof. intros rho. eapply mergeTermProto. now intros v. Defined.

  Definition mergeFormBase (c:preds) : Type := 
  forall (rho:nat -> D), @nary3GFunc (ar_preds c) term D form (naryProp 0) 
                                     (fun t d => representsF d t rho) (fun t P => representsP t rho P) 
                                     (atom c) (@i_atom fs ps D I c).
  Definition mergeFormProtoType (rho:nat -> D) (n:nat) (fZ:Vector.t term n -> form) (ifZ : Vector.t D n -> naryProp 0) := 
         (forall v : Vector.t term n, @sat fs ps D I ff rho (fZ v) = ifZ (Vector.map (@eval fs ps D I rho) v))  
         -> @nary3GFunc n term D form (naryProp 0) (fun t d => representsF d t rho) (fun t P => representsP t rho P) fZ ifZ.
  (* Proof that the functions built using the above helper actually represent the syntactic construct they are supposed to represent *)
  Definition mergeFormProto (rho:nat -> D) (n:nat) (fZ:Vector.t term n -> form) (ifZ : Vector.t D n -> naryProp 0) : @mergeFormProtoType rho n fZ ifZ.
  Proof.
  intros H. induction n as [|n IH].
  * cbn. unfold representsP. rewrite H. cbn. easy.
  * cbn. intros t d r. apply IH. cbn. intros v. specialize (H (Vector.cons t v)). unfold representsF in r. rewrite H. cbn. now rewrite r.
  Defined.
  Definition mergeForm (c:preds) : mergeFormBase c.
  Proof. intros rho. eapply mergeFormProto. now intros v. Defined.
  (*+ Quotes of these functions which are later used to construct (proof) terms *)
  MetaCoq Quote Definition qConstructTerm := constructTerm.
  MetaCoq Quote Definition qMergeTerm := mergeTerm.
  MetaCoq Quote Definition qConstructForm := constructForm.
  MetaCoq Quote Definition qMergeForm := mergeForm.
End AbstractReflectionDefinitions.
#[global] Arguments representableP {_} {_} _ _.

Section TarskiMerging.
  (* **TarskiMerging
        Here we have reifiers for basic logical connectives which are part of the core Tarski semantics and thus every model.
        These are and, or, falsity, implication and both quantifiers *)
  Context {tr : tarski_reflector}.
  Context {te : tarski_reflector_extensions tr}.
  (* Hack to get these to use the proper type class instance *)
  Notation term := (@Core.term (@fs tr)).
  Notation form ff := (@Core.form (@fs tr) (@ps tr) full_operators ff).
  Notation syms := (@Core.syms (@fs tr)).
  Notation preds := (@Core.preds (@ps tr)).

  (* For each connective, we have a "merger" that takes subproof that a term is represented by its reification, and proof that the larger term also represents its subterm.
      For falsity, there are not subterms, so we just prove that fal represents False, which is trivial *)
  Definition mFalse : form falsity_on := falsity.
  Definition mergeFalse (rho:nat -> D) : @representsP tr falsity_on 0 falsity rho False.
  Proof. easy. Defined.
  (* We then define a quoted version of the above proof which is later used to build subterms *)
  MetaCoq Quote Definition qMergeFalse := @mergeFalse. 
  (* We finally define a quoted form merger which will then later be applied to the subforms. It should yield the reflected representation *)
  MetaCoq Quote Definition qMergeFormFalse := @mFalse.
  (* The same development for And. Note that this time we have subproofs. Our function arguments follow this pattern:
      - tr_quoted - quoted tarski_reflector (not visible in the arguments, but it's a context variable. Note that since the functions don't acually use te, it does not become part of the arguments outside the section
      - environment
      - coq subterms that are to be reified
      - reified subterms
      - proof that the reified subterms are actually the reifications *)
  Definition mAnd {ff : falsity_flag} (fP fQ:form ff) : form ff := fP∧fQ.
  Definition mergeAnd {ff : falsity_flag} (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form ff) : representsP fP rho P -> representsP fQ rho Q -> @representsP tr ff 0 (mAnd fP fQ) rho (P /\ Q).
  Proof.
  intros [pPl pPr] [pQl pQr]. split.
  * intros [pP pQ]. split. now apply pPl. now apply pQl.
  * intros [pP pQ]. split. now apply pPr. now apply pQr.
  Defined.
  MetaCoq Quote Definition qMergeAnd := @mergeAnd.
  (* This is the form merger for and. It is unfolded syntactic sugar, once one adds the arguments x and y, this will read x ∧ y. *)
  MetaCoq Quote Definition qMergeFormAnd := @mAnd.

  (* The same development for or*)
  Definition mOr {ff : falsity_flag} (fP fQ:form ff) : form ff := fP∨fQ.
  Definition mergeOr {ff : falsity_flag} (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form ff) : representsP fP rho P -> representsP fQ rho Q -> @representsP tr ff 0 (mOr fP fQ) rho (P \/ Q).
  Proof.
  intros [pPl pPr] [pQl pQr]. split.
  * intros [pP|pQ]. left; now apply pPl. right; now apply pQl.
  * intros [pP|pQ]. left; now apply pPr. right; now apply pQr.
  Defined.
  MetaCoq Quote Definition qMergeOr := @mergeOr.
  MetaCoq Quote Definition qMergeFormOr := @mOr.

  (* The same development for existential quantifiaction. Note that the P argument is a 1-ary predicate.*)
  Definition mExists {ff : falsity_flag} (fP:form ff) : form ff := ∃ fP.
  Definition mergeExists {ff : falsity_flag} (rho:nat -> D) (P:naryProp 1) (fP:form ff) : representsP fP rho P -> @representsP tr ff 0 (mExists fP) rho (exists q:D, P q).
  Proof.
  intros pR. split.
  * intros [q Pq]. exists q. destruct (pR q) as [pRl pRr]. now apply pRl.
  * intros [q Pq]. exists q. destruct (pR q) as [pRl pRr]. now apply pRr.
  Defined.
  MetaCoq Quote Definition qMergeExists := @mergeExists.
  MetaCoq Quote Definition qMergeFormExists := @mExists.

  (* The same development for implication. Note that implication is handled in the main reification logic since P -> Q is just syntactic sugar for (forall _:P, Q)*)
  Definition mImpl {ff : falsity_flag} (fP fQ : form ff) : form ff := fP → fQ.
  Definition mergeImpl {ff : falsity_flag} (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form ff) : representsP fP rho P -> representsP fQ rho Q -> @representsP tr ff 0 (mImpl fP fQ) rho (P -> Q).
  Proof.
  intros HP HQ.
  destruct HP as [pPl pPr]. destruct HQ as [pQl pQr]. split.
  * intros PQ pP. apply pQl, PQ, pPr, pP.
  * cbn. intros pPQ pP. apply pQr, pPQ, pPl, pP.
  Defined.
  MetaCoq Quote Definition qMergeImpl := @mergeImpl.
  MetaCoq Quote Definition qMergeFormImpl := @mImpl.

  (* The same development for forall. Since forall-quantification in Coq is a part of the proper syntax (product types), this will again be handled by the main reification*)
  Definition mForall {ff : falsity_flag} (fP:form ff) : form ff := ∀ fP.
  Definition mergeForall {ff : falsity_flag} (rho:nat -> D) (Q:naryProp 1) (phi:form ff) : representsP phi rho Q -> @representsP tr ff 0 (mForall phi) rho (forall x:D, Q x).
  Proof. intros H. cbn. split;
   intros HH d; specialize (HH d); specialize (H d); cbn in H; apply H, HH.
  Defined.
  MetaCoq Quote Definition qMergeForall := @mergeForall.
  MetaCoq Quote Definition qMergeFormForall := @mForall.

  Definition mIff {ff : falsity_flag} (fP fQ : form ff) : form ff := fP ↔ fQ.
  Definition mergeIff {ff : falsity_flag} (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form ff) : representsP fP rho P -> representsP fQ rho Q -> @representsP _ ff 0 (mIff fP fQ) rho (P <-> Q).
  Proof. intros H1 H2. cbn. cbn in H1,H2. rewrite H2, H1. reflexivity. Defined.
  MetaCoq Quote Definition qMergeFormIff := @mIff.
  MetaCoq Quote Definition qMergeIff := @mergeIff. 

  (* The same development for not X. *)
  Definition mNot (fP : form falsity_on) : form falsity_on := fP→falsity.
  Definition mergeNot (rho:nat -> D) (P:naryProp 0) (fP : form falsity_on) : @representsP _ falsity_on 0 fP rho P -> @representsP _ falsity_on 0 (mNot fP) rho (~P).
  Proof. cbn. tauto. Defined.
  MetaCoq Quote Definition qMergeFormNot := @mNot.
  MetaCoq Quote Definition qMergeNot := @mergeNot.


  (* The same development for truth. Note that truth has no canonical representative in the tarski semantics. It is equivalent to (falsity -> falsity), but not computationally equal. So using True in noProof mode would fail.*)
  Definition mTrue : form falsity_on := falsity → falsity.
  Definition mergeTrue (rho:nat -> D) : @representsP _ falsity_on 0 (mTrue) rho (True).
  Proof. cbn. tauto. Defined.
  MetaCoq Quote Definition qMergeFormTrue := @mTrue.
  MetaCoq Quote Definition qMergeTrue := @mergeTrue.

  (* Notation for matching constructs like Coq.Init.Logic.and prop1 prop2 -> (x:="and", l:=[term1, term2]) *)
  Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
  (* We now define reification helpers for each of the primitives (except implication&forall). These helpers recursively apply the main reification function to the subterms and assemble the resulting term/prood*)
  Definition reifyFalse : baseConnectiveReifier := fun tct qff lst _ envTerm env fPR _ => match lst with nil => ret (tApp qMergeFormFalse ([tct]), tApp qMergeFalse ([tct;envTerm])) | _ => fail "False applied to terms" end. 
  Definition reifyAnd : baseConnectiveReifier := fun tct qff lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xr <- fPR qff x 0 envTerm env;;yr <- fPR qff y 0 envTerm env;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                             ret (tApp qMergeFormAnd ([tct;qff;xt;yt]), tApp qMergeAnd ([tct;qff;envTerm;x;y;xt;yt;xp;yp])) | _ => fail "And applied to != 2 terms" end.
  Definition reifyOr  : baseConnectiveReifier := fun tct qff lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xr <- fPR qff x 0 envTerm env;;yr <- fPR qff y 0 envTerm env;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                             ret (tApp qMergeFormOr ([tct;qff;xt;yt]),tApp qMergeOr ([tct;qff;envTerm;x;y;xt;yt;xp;yp])) | _ => fail "Or applied to != 2 terms" end.
  Definition reifyExist:baseConnectiveReifier := fun tct qff lst _ envTerm env fPR _ => match lst with [_; P] => 
                                             rr <- fPR qff P 1 envTerm env;; let '(rt,rp) := rr in 
                                             ret (tApp qMergeFormExists ([tct;qff;rt]), tApp qMergeExists ([tct;qff;envTerm;P;rt;rp])) | _ => fail "Exist applied to wrong terms" end.
  Definition reifyIff : baseConnectiveReifier := fun tct qff lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xr <- fPR qff x 0 envTerm env;;yr <- fPR qff y 0 envTerm env;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                             ret (tApp qMergeFormIff ([tct;qff;xt;yt]), tApp qMergeIff ([tct;qff;envTerm;x;y;xt;yt;xp;yp])) | _ => fail "Iff applied to != 2 terms" end.
  Definition reifyNot  : baseConnectiveReifier := fun tct qff lst _ envTerm env fPR _ => match lst with [x] => 
                                             xr <- fPR qff x 0 envTerm env;; let '(xt,xp) := xr in
                                             ret (tApp qMergeFormNot ([tct;xt]),tApp qMergeNot ([tct;envTerm;x;xt;xp])) | _ => fail "not applied to != 1 terms" end.
  Definition reifyTrue : baseConnectiveReifier := fun tct qff l fuel envTerm env fPR _ => match l with nil =>
                                             ret (tApp qMergeFormTrue ([tct]), tApp qMergeTrue ([tct;envTerm]))| _ => fail "True applied to terms" end.
  (* The main handler. Given the name of the base type, call the respective helper. If nothing matches, call the extension point *)
  Definition reifyBase (s:string): baseConnectiveReifier 
                            := match s with "and" => reifyAnd | "or" => reifyOr | "ex" => reifyExist |  "False" => reifyFalse | "True" => reifyTrue |
                                       _ => match baseLogicConnHelper with 
                                             None =>fun _ _ _ _ _ _ _ _ => fail ("Unknown connective "++s) | 
                                             Some k => k s end end.
  (* The same development for no-proof mode. Similar, except we don't build proofs *)
  Definition baseConnectiveReifierNP := Ast.term -> Ast.term -> list Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> 
                                       (Ast.term -> Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad ( Ast.term)) -> 
                                       (Ast.term -> Ast.term -> Ast.term -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad (Ast.term)) -> FailureMonad (Ast.term).
  Definition reifyFalseNP : baseConnectiveReifierNP := fun tct qff lst _ envTerm env fPR _ => match lst with nil => ret (tApp qMergeFormFalse ([tct])) | _ => fail "False applied to terms" end. 
  Definition reifyAndNP : baseConnectiveReifierNP := fun tct qff lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xt <- fPR qff x 0 envTerm env;;yt <- fPR qff y 0 envTerm env;; 
                                             ret (tApp qMergeFormAnd ([tct;qff;xt;yt])) | _ => fail "And applied to != 2 terms" end.
  Definition reifyOrNP  : baseConnectiveReifierNP := fun tct qff lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xt <- fPR qff x 0 envTerm env;;yt <- fPR qff y 0 envTerm env;; 
                                             ret (tApp qMergeFormOr ([tct;qff;xt;yt])) | _ => fail "Or applied to != 2 terms" end.
  Definition reifyExistNP:baseConnectiveReifierNP := fun tct qff lst _ envTerm env fPR _ => match lst with [_; P] => 
                                             rt <- fPR qff P 1 envTerm env;;
                                             ret (tApp qMergeFormExists ([tct;qff;rt])) | _ => fail "Exist applied to wrong terms" end.
  Definition reifyIffNP : baseConnectiveReifierNP := fun tct qff lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xt <- fPR qff x 0 envTerm env;;yt <- fPR qff y 0 envTerm env;;
                                             ret (tApp qMergeFormIff ([tct;qff;xt;yt])) | _ => fail "Iff applied to != 2 terms" end.
  Definition reifyNotNP : baseConnectiveReifierNP := fun tct qff l fuel envTerm env fPR _ => match l with [x] =>
                                             xt <- fPR qff x 0 envTerm env;;
                                             ret (tApp qMergeFormNot ([tct;xt]))| _ => fail "not applied to != 1 terms" end.
  Definition reifyTrueNP : baseConnectiveReifierNP := fun tct qff l fuel envTerm env fPR _ => match l with nil =>
                                             ret (tApp qMergeFormTrue ([tct]))| _ => fail "True applied to terms" end.
  (* The helper is a bit more interesting, since it calls the extension point, building a recursive "dummy proof" helper and discarding the resulting proof *)
  Definition reifyBaseNP (s:string): baseConnectiveReifierNP 
                            := match s with "and" => reifyAndNP | "or" => reifyOrNP | "ex" => reifyExistNP |  "False" => reifyFalseNP |  "True" => reifyTrueNP | 
                                       _ => match baseLogicConnHelper with 
                                             None =>fun _ _ _ _ _ _ _ _ => fail ("Unknown connective "++s) | 
                                             Some k => fun tct qff lst fuel envTerm env fPR fTR => both <- k s tct qff lst fuel envTerm env 
                                                                                                        (fun qff P n et e => rr <- fPR qff P n et e;; ret (rr, noProofDummy)) 
                                                                                                        (fun tct qff t eT env => rr <- fTR tct qff t eT env;; ret (rr, noProofDummy));; 
                                                                  let '(trm,_) := both in ret trm end end.
End TarskiMerging.

Section ReificationHelpers.
  (* **ReificationHelpers
      These functions reify atomic functions/relations *)
  (* Definition of the types. The arguments are:
      - tct:Ast.term - quoted instance of tarski_reflector
      - qff:Ast.term -- the instance of falsity_flag
      - av:list Ast.term - the arguments of an atomic relation/function to be recursively reified
      - envTerm
      - recursive helper, to which av is passed one-by-one
      - the return is again either a pair of term&proof, or just the term if in no proof mode *)
  Definition termReifier := Ast.term -> Ast.term -> list Ast.term -> Ast.term -> (Ast.term -> FailureMonad (prod Ast.term Ast.term)) -> FailureMonad (prod Ast.term Ast.term).
  Definition termReifierNP := Ast.term -> Ast.term -> list Ast.term -> Ast.term -> (Ast.term -> FailureMonad (Ast.term)) -> FailureMonad (Ast.term).
  (* Args: typeClassTerm -> vector of args -> env term -> recursion for arg vector -> prod (term, proof that term represents input *)
  Fixpoint applyRecursively (lt : list Ast.term) (IH : Ast.term -> FailureMonad (prod Ast.term Ast.term)) : FailureMonad (prod (list Ast.term) (list Ast.term)) :=
     match lt with nil => ret (nil,nil)
               | t::tr => IHt <- IH t;; atrIH <- applyRecursively tr IH;;let '(rep,prf) := IHt in let '(replist,fulllist) := atrIH in ret (rep::replist, rep::t::prf::fulllist) end.
  Fixpoint applyRecursivelyNP (lt : list Ast.term) (IH : Ast.term -> FailureMonad (Ast.term)) : FailureMonad ((list Ast.term) ) :=
     match lt with nil => ret (nil)
               | t::tr => rep <- IH t;; replist <- applyRecursivelyNP tr IH;;ret (rep::replist) end.
  Definition reifyTerm (c:Ast.term) : termReifier := fun tct qff av env IH => pr <- applyRecursively av IH;; let '(trm,fullarg) := pr in
                                                     ret (tApp qConstructTerm (tct::c::trm), tApp qMergeTerm (tct::c::env::fullarg)).
  Definition reifyForm (c:Ast.term) : termReifier := fun tct qff av env IH => pr <- applyRecursively av IH;; let '(trm,fullarg) := pr in
                                                     ret (tApp qConstructForm (tct::qff::c::trm), tApp qMergeForm (tct::qff::c::env::fullarg)).
  Definition reifyTermNP (c:Ast.term) : termReifierNP := fun tct qff av env IH => trm <- applyRecursivelyNP av IH;; 
                                                     ret (tApp qConstructTerm (tct::c::trm)).
  Definition reifyFormNP (c:Ast.term) : termReifierNP := fun tct qff av env IH => trm <- applyRecursivelyNP av IH;; 
                                                     ret (tApp qConstructForm (tct::qff::c::trm)).
End ReificationHelpers.

Section EnvHelpers.
  (* ** EnvHelpers
      Useful functions for extending the environment. A 3-ary predicate P(k1,k2,k3) (for example) is represented by a term t where t in environ (k3:k2:k1:env) represents P (k1,k2,k3).*)
  (* Appends something to the start of the env. *)
  Definition appendZero (env:Ast.term -> FailureMonad nat) (zv:FailureMonad nat) : (Ast.term -> FailureMonad nat) := 
        fun (t:Ast.term) => match t with tRel n => (match n with 0 => zv | S n => env (tRel n) end) | _ => k <- lowerRelIndex 0 (fail "tRel 0 used when lowering") t;; (env k) end.
  (* Appends something to the start of the env. At the same time, it expects the terms given to the env helper to be one level deeper, so it "unshifts" the tRels first *)
  Definition appendAndLift (env:Ast.term -> FailureMonad nat) (zv:FailureMonad nat) : (Ast.term -> FailureMonad nat) := 
        fun t => match t with tRel n => (match n with 0 => zv | S n => k <- env (tRel n);;ret (S k) end) | _ => k <- lowerRelIndex 0 (fail "tRel 0 used when lowering") t;; v <- env k;;ret (S v) end.
  MetaCoq Quote Definition qD := @D.
  MetaCoq Quote Definition qScons := @scons.
  (* Appends d to the env *)
  Definition raiseEnvTerm (tct:Ast.term) (d:Ast.term) (env:Ast.term) : Ast.term := tApp (qScons) ([tApp qD ([tct]);d;env]).
  (* The env helper for the empty environ, which always fails *)
  Definition unboundEnv := (fun a:Ast.term => @fail nat ("unbound " ++ string_of_term a)).
End EnvHelpers.

Section EnvConstructor.
  (* ** EnvConstructor
      Constructs the environment used to help with free variables in terms *)
  (* Useful quotations *)
  Existing Instance config.default_checker_flags.
  MetaCoq Quote Definition qFs := @fs.
  MetaCoq Quote Definition qLocalVar := @var.
  MetaCoq Quote Definition qI_f := @i_func.
  MetaCoq Quote Definition qI_P := @i_atom.
  Context {tr : tarski_reflector}.
  Context {te : tarski_reflector_extensions tr}.
  (* Given a term in the semantic, construct an environment that contains all atoms that appear in the term (and are not otherwise representable) *)
  Fixpoint findUBRecursively (lt : list Ast.term) (IH : Ast.term -> FailureMonad (list Ast.term)) : FailureMonad ((list Ast.term) ) :=
       match lt with nil => ret (nil)
                 | t::tr => rep <- IH t;; replist <- findUBRecursively tr IH;;ret (rep++replist) end.
  (* Finds all free variables in a term *)
  Fixpoint findUnboundVariablesTerm (fuel:nat) (t:Ast.term) {struct fuel}: (FailureMonad (list Ast.term)) := match fuel with 
      0 => fail "Out of fuel" 
      | S fuel => let ffail := orelse (match @termReifierVarHelper _ te with None => fail "Fallthrough" | Some k => k fuel t (findUnboundVariablesTerm fuel) end)
                        (match t with tRel _ => ret nil | _ => ret ([t]) end) in (* tRel are things introduced by forall/exists and so on, which we do not add to the environment *)
          match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;findUBRecursively vr (findUnboundVariablesTerm fuel)
           | _ => ffail end else ffail
        | _ => ffail
      end 
    end.
  (*Our notation from above*)
  Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
  (* Find the unbound variables for our basic forms *)
  Definition findUBFalse  :baseConnectiveVars := fun lst _ _ fPR _ => match lst with nil => 
                                             ret (nil) | _ => fail "False applied to terms" end.
  Definition findUBAnd  :baseConnectiveVars := fun lst _ _ fPR _ => match lst with [x; y] => 
                                             xt <- fPR x 0;;yt <- fPR y 0;; 
                                             ret (xt++yt) | _ => fail "And applied to != 2 terms" end.
  Definition findUBOr   :baseConnectiveVars := fun lst _ _ fPR _ => match lst with [x; y] => 
                                             xt <- fPR x 0;;yt <- fPR y 0;; 
                                             ret (xt++yt) | _ => fail "Or applied to != 2 terms" end.
  Definition findUBExists:baseConnectiveVars := fun lst _ _ fPR _ => match lst with [_; P] => fPR P 1 | _ => fail "Exist applied to wrong terms" end.
  Definition findUBNot  :baseConnectiveVars := fun lst _ _ fPR _ => match lst with [k] => fPR k 0 | _ => fail "not applied to wrong terms" end.
  Definition findUBTrue : baseConnectiveVars := fun lst fuel tct _ _ => match lst with nil => ret nil | _ => fail "True applied to terms" end.
  Definition findUBIff  :baseConnectiveVars := fun lst _ _ fPR _ => match lst with [x; y] => 
                                           xt <- fPR x 0;;yt <- fPR y 0;; 
                                           ret (xt++yt) | _ => fail "Iff applied to != 2 terms" end.

  Definition findUBBase (s:string) : baseConnectiveVars 
          := match s with "and" => findUBAnd | "or" => findUBOr | "ex" => findUBExists | "False" => findUBFalse | "True" => findUBTrue | _ => 
                match @baseLogicVarHelper tr te with None => fun _ _ _ _ _ => fail ("Unknown connective "++s) | Some k => k s end end.
  MetaCoq Quote Definition qIff := @iff.
  MetaCoq Quote Definition qNot := @not.
  (* Checks whether a term is the type of theory terms in Coq. *)
  Definition maybeD : Ast.term -> Ast.term -> bool := fun tct mD => if @isD tr mD then true else Checker.eq_term init_graph mD (tApp qD ([tct])).
  (* Finds the unbound variables in a form *)
  Fixpoint findUnboundVariablesForm (tct:Ast.term) (fuel:nat) (t:Ast.term) (frees:nat) {struct fuel}: (FailureMonad (list Ast.term)) := 
  let ffail := fail ("Cannot introspect form "++ string_of_term t) in match fuel with 0 => fail "Out of fuel" | S fuel => 
    match (frees,t) with
    (0,(baseLogicConn name nil)) => findUBBase name nil fuel tct (findUnboundVariablesForm tct fuel) (findUnboundVariablesTerm fuel)
  | (0,(tApp (baseLogicConn name nil) lst)) => findUBBase name lst fuel tct (findUnboundVariablesForm tct fuel) (findUnboundVariablesTerm fuel)
  | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
          Some ([fnc;v]) => vr <- recoverVector v;;findUBRecursively vr (fun t => findUnboundVariablesTerm fuel t)
        | _ => ffail  end else if Checker.eq_term init_graph arg qIff then findUBIff lst fuel tct (findUnboundVariablesForm tct fuel) (findUnboundVariablesTerm fuel) 
                          else if Checker.eq_term init_graph arg qNot then findUBNot lst fuel tct (findUnboundVariablesForm tct fuel) (findUnboundVariablesTerm fuel) else ffail 
  | (0,tProd x P Q) => if maybeD tct (P) then
                            findUnboundVariablesForm tct fuel (tLambda x P Q) 1
                       else (*implication*)
                            rP <- findUnboundVariablesForm tct fuel P 0;;
                            Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                            rQ <- findUnboundVariablesForm tct fuel Ql 0;;
                            ret (rP++rQ)
  | (S n,tLambda x T P) => if maybeD tct T then
        findUnboundVariablesForm tct fuel P n
       else ffail
  | _ => ffail  end end.

  Fixpoint isIn (l:list Ast.term) (x:Ast.term) := match l with nil=>false | lx::lr => if Checker.eq_term init_graph lx x then true else isIn lr x end.
  Fixpoint dedup (l:list Ast.term) := match l with nil => nil | lx::lr => if isIn lr lx then dedup lr else lx::dedup lr end.

 (* Builds the actual env out of a list of free variables *)
 Fixpoint createEnvTerms (tct:Ast.term) (l:list Ast.term) (base:Ast.term) : prod (Ast.term) (Ast.term -> FailureMonad nat) := match l with 
       nil => (base,unboundEnv)
   | x::xr => let '(envTerm,env) := createEnvTerms tct xr base in (raiseEnvTerm tct x envTerm, fun a:Ast.term => if Checker.eq_term init_graph x a then ret 0 else v <- env a;;ret (S v)) end.
End EnvConstructor.

Section MainReificationFunctions.
  (* ** MainReificationFunctions
  Constructs the actual reifications, putting everything together *)
  Context {tr : tarski_reflector}.
  Context {te : tarski_reflector_extensions tr}.
  Existing Instance config.default_checker_flags.
  (* *** Terms 
   Constructs the representation for terms.*)
  (* Arguments:
      - tct -- the quoted instance of tarski_reflector
      - fuel -- fuel
      - qff -- the quoted instance of falsity_flag
      - t -- the term to reify
      - termEnv -- the env term
      - env -- the env helper
      - returns the pair of reification/proof *) 
  Fixpoint findTermRepresentation (tct:Ast.term) (fuel:nat) (qff:Ast.term) (t:Ast.term) (termEnv:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (prod Ast.term Ast.term)) := match fuel with 
      0 => fail "Out of fuel" 
      | S fuel =>
    let fallback := orelse (match @termReifierReifyHelper _ te with None => fail "none" | Some k => k tct qff fuel t termEnv env (fun l => findTermRepresentation l fuel) end)
                           (envv <- env (t);;let num := quoteNumber (envv) in ret (tApp qLocalVar ([tApp qFs ([tct]);num]),tApp qeq_refl ([tApp qD ([tct]);t]))) in match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;reifyTerm fnc tct qff vr termEnv (fun t => findTermRepresentation tct fuel qff t termEnv env)
           | _ => fallback end else fallback
        | _ => fallback
      end 
    end.
  (* Like the above, but without the proof *)
  Fixpoint findTermRepresentationNP (tct:Ast.term) (fuel:nat) (qff:Ast.term) (t:Ast.term) (termEnv:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (Ast.term)) := match fuel with 
      0 => fail "Out of fuel" 
      | S fuel =>
    let fallback := orelse (match @termReifierReifyHelper _ te with None => fail "none" | Some k => pr <- k tct qff fuel t termEnv env (fun tct' qff' t' te' e' => v <- findTermRepresentationNP tct' fuel qff' t' te' e';;ret (v,noProofDummy));; let '(pr1,pr2) := pr in ret pr1 end)
                           (envv <- env (t);;let num := quoteNumber (envv) in ret (tApp qLocalVar ([tApp qFs ([tct]);num]))) in match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;reifyTermNP fnc tct qff vr termEnv (fun t => findTermRepresentationNP tct fuel qff t termEnv env)
           | _ => fallback end else fallback
        | _ => fallback
      end 
    end.

    Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
   (* *** Forms *)
    (* Like the above, but here we do it for forms. Arguments:
       - tct -- like above
       - fuel -- like above
       - qff -- like above
       - t -- the term
       - frees: the arity of the form we are reifying. If nonzero, the form must be a lambda term
       - envTerm -- the env, quoted
       - env -- the env helper *)
    Fixpoint findPropRepresentation (tct:Ast.term) (fuel:nat) (qff:Ast.term) (t:Ast.term) (frees:nat) (envTerm:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (prod Ast.term Ast.term)) := 
    match fuel with 0 => fail "Out of fuel" | S fuel => 
      let ffail := orelse (match @formReifierReifyHelper _ te with None => fail "none" | Some k => k tct qff fuel t frees envTerm env (findPropRepresentation tct fuel) (fun l => findTermRepresentation l fuel) end) 
                        (fail ("Cannot represent form " ++ string_of_term t)) in match (frees,t) with
      (0,(baseLogicConn name nil)) => reifyBase name tct qff nil fuel envTerm env (findPropRepresentation tct fuel) (fun tct => findTermRepresentation tct fuel)
    | (0,(tApp (baseLogicConn name nil) lst)) => reifyBase name tct qff lst fuel envTerm env (findPropRepresentation tct fuel) (fun tct => findTermRepresentation tct fuel)
    | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
            Some ([fnc;v]) => vr <- recoverVector v;;reifyForm fnc tct qff vr envTerm (fun t => findTermRepresentation tct fuel qff t envTerm env)
          | _ => ffail end else if Checker.eq_term init_graph arg qIff then reifyIff tct qff lst fuel envTerm env (findPropRepresentation tct fuel) (fun tct => findTermRepresentation tct fuel) 
                           else if Checker.eq_term init_graph arg qNot then reifyNot tct qff lst fuel envTerm env (findPropRepresentation tct fuel) (fun tct => findTermRepresentation tct fuel) 
                           else ffail
    | (0,tProd x P Q) => if maybeD tct (P) then
                              rQ <- findPropRepresentation tct fuel qff (tLambda x P Q) 1 envTerm env;; let '(tQ,pQ) := rQ in
                              ret (tApp qMergeFormForall ([tct;qff;tQ]), tApp qMergeForall ([tct;qff;envTerm;tLambda x P Q;tQ;pQ]))
                         else
                              rP <- findPropRepresentation tct fuel qff P 0 envTerm env;;
                              Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                              rQ <- findPropRepresentation tct fuel qff Ql 0 envTerm env;; let '((tP,pP),(tQ,pQ)) := (rP,rQ) in
                              ret (tApp qMergeFormImpl ([tct;qff;tP;tQ]), tApp qMergeImpl ([tct;qff;envTerm;P;Ql;tP;tQ;pP;pQ]))
    | (S n,tLambda x T P) => if maybeD tct T then
          let envTermSub := raiseEnvTerm tct (tRel 0) (addRelIndex 0 1 envTerm) in
          let envSub := appendAndLift env (ret 0) in
          k <- findPropRepresentation tct fuel qff P n envTermSub envSub;; let '(tk,pk) := k in
          ret (tk,(tLambda x (tApp qD ([tct])) pk))
         else ffail
    | _ => ffail end end.
    (* like the above but again the no-proof version *)
    Fixpoint findPropRepresentationNP (tct:Ast.term) (fuel:nat) (qff:Ast.term) (t:Ast.term) (frees:nat) (envTerm:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (Ast.term)) := 
    match fuel with 0 => fail "Out of fuel" | S fuel => 
      let ffail := orelse (match @formReifierReifyHelper _ te with None => fail "none" | Some k => rr <- k tct qff fuel t frees envTerm env (fun qff' t f et e => v <- findPropRepresentationNP tct fuel qff' t f et e;; ret (v,noProofDummy)) (fun l qff' t et e => v <- findTermRepresentationNP l fuel qff' t et e;;ret (v,noProofDummy));;let '(trm,_) := rr in ret trm end)  
                          (fail ("Cannot represent form " ++ string_of_term t)) in match (frees,t) with
      (0,(baseLogicConn name nil)) => reifyBaseNP name tct qff nil fuel envTerm env (findPropRepresentationNP tct fuel) (fun tct => findTermRepresentationNP tct fuel)
    | (0,(tApp (baseLogicConn name nil) lst)) => reifyBaseNP name tct qff lst fuel envTerm env (findPropRepresentationNP tct fuel) (fun tct => findTermRepresentationNP tct fuel)
    | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
            Some ([fnc;v]) => vr <- recoverVector v;;reifyFormNP fnc tct qff vr envTerm (fun t => findTermRepresentationNP tct fuel qff t envTerm env)
          | _ => ffail end else if Checker.eq_term init_graph arg qIff then reifyIffNP tct qff lst fuel envTerm env (findPropRepresentationNP tct fuel) (fun tct => findTermRepresentationNP tct fuel) 
                           else if Checker.eq_term init_graph arg qNot then reifyNotNP tct qff lst fuel envTerm env (findPropRepresentationNP tct fuel) (fun tct => findTermRepresentationNP tct fuel) 
                           else ffail
    | (0,tProd x P Q) => if maybeD tct (P) then
                              tQ <- findPropRepresentationNP tct fuel qff (tLambda x P Q) 1 envTerm env;; 
                              ret (tApp qMergeFormForall ([tct;qff;tQ]))
                         else
                              tP <- findPropRepresentationNP tct fuel qff P 0 envTerm env;;
                              Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                              tQ <- findPropRepresentationNP tct fuel qff Ql 0 envTerm env;; 
                              ret (tApp qMergeFormImpl ([tct;qff;tP;tQ]))
    | (S n,tLambda x T P) => if maybeD tct T then
          let envTermSub := raiseEnvTerm tct (tRel 0) (addRelIndex 0 1 envTerm) in
          let envSub := appendAndLift env (ret 0) in
          tk <- findPropRepresentationNP tct fuel qff P n envTermSub envSub;;
          ret (tk)
         else ffail
    | _ => ffail end end.
End MainReificationFunctions.

(* Default fuel. This is enough for all terms with depth 100 *)
Definition FUEL := 100.
(* ** Tactics
 All tactics expect the goal to be representable n P *)
(* Tactic that calls findPropRepresentation. Given an env (unquoted) and a respective env helper *)
Ltac representEnvP env env2:= 
match goal with [ |- @representableP ?i ?ff ?n ?G ] => 
  let rep := fresh "rep" in let prf := fresh "prf" in let k y := (destruct y as [rep prf]) in
  (*pose ((match env1 with None => @emptyEnv i | Some kk => kk end)) as env;*)
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmQuote ff) (fun qff => 
                         monad_utils.bind (tmInferInstance None (tarski_reflector_extensions i)) (fun treO => let tre := match treO with my_Some kk => kk | my_None => defaultExtensions i end in
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t (@findPropRepresentation i tre tct FUEL qff g n qe env2)) (fun '(tPq,pPq) => 
                         monad_utils.bind (tmUnquoteTyped (@form (@fs i) (@ps i) full_operators ff) tPq) (fun tP:(@form (@fs i) (@ps i) full_operators ff) => 
                         monad_utils.bind (tmUnquoteTyped (@representsP i ff n tP env G) pPq) (fun tQ : @representsP i ff n tP env G =>
                         monad_utils.ret (@existT (@form (@fs i) (@ps i) full_operators ff) (fun mm => @representsP i ff n mm env G) tP tQ)))))))))) k)
  ;exists rep;exists env;exact prf 
end.
(* Like the above, but no-proof mode. We hope easy can proof it, if not the user must close (or alternatively try  representEnvP )*)
Ltac representEnvPNP env env2:= 
match goal with [ |- @representableP ?i ?ff ?n ?G ] => 
  let rep := fresh "rep" in let prf := fresh "prf" in let k y := (pose y as rep) in
  (*pose ((match env1 with None => @emptyEnv i | Some kk => kk end)) as env;*)
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmQuote ff) (fun qff => 
                         monad_utils.bind (tmInferInstance None (tarski_reflector_extensions i)) (fun treO => let tre := match treO with my_Some kk => kk | my_None => defaultExtensions i end in
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t ((@findPropRepresentationNP i tre tct FUEL qff g n qe env2))) (fun tPq => 
                         monad_utils.bind (tmUnquoteTyped (@form (@fs i) (@ps i) full_operators ff) tPq) (fun tP:(@form (@fs i) (@ps i) full_operators ff) => 
                         monad_utils.ret (tP))))))))) k)
  ;exists rep;exists env;try easy 
end.

(* Construct the environment, then invoke another ltac with the build environment and the respective env helper (continuation-passing style) *)
Definition HiddenTerm {X:Type} {x:X} := x.
Ltac constructEnvCont cont := 
match goal with [ |- @representableP ?i ?ff ?n ?G ] => (*(pose (fst y) as envBase;pose (snd y) as envTerm*)
  (*let envBase := fresh "envBase" in let envTerm := fresh "envTerm" in *)
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmQuote ff) (fun qff => 
                         monad_utils.bind (tmInferInstance None (tarski_reflector_extensions i)) (fun treO => let tre := match treO with my_Some kk => kk | my_None => defaultExtensions i end in
                         monad_utils.bind (tmQuote (@emptyEnv i)) (fun baseEnv => 
                         monad_utils.bind (f2t ((@findUnboundVariablesForm i tre tct FUEL g n))) (fun lst => 
                         let '(envToDR,envToNat) := (createEnvTerms tct (dedup lst) baseEnv) in
                         monad_utils.bind (tmUnquoteTyped (nat -> @D i) envToDR) (fun envToD => 
                         monad_utils.ret (pair envToD envToNat))))))))) cont)
end.
(* Construct the env, then bind it to envBase and envTerm. Useful if one does not actually want to show representability with the automation but just build the environment*)
Ltac constructEnv' envBase envTerm := match goal with [ |- @representableP ?i ?ff ?n ?G ] => let k y := (pose (@HiddenTerm (nat -> @D i) (fst y)) as envBase;pose (@HiddenTerm (Ast.term -> FailureMonad nat) (snd y)) as envTerm) in constructEnvCont k end. 
Ltac constructEnv := let envBase := fresh "envBase" in let envTerm := fresh "envTerm" in constructEnv' envBase envTerm.

(* The main tactic. Builds an environment, finds a reification and a proof of correctness. Calls the above tactics *)
Ltac represent := match goal with [ |- @representableP ?i ?ff ?n ?G ] => let tac k := (let envBase := fresh "envBase" in (pose (@HiddenTerm (nat -> @D i) (fst k)) as envBase); representEnvP envBase (snd k)) in constructEnvCont tac end.
(* The same, but without the proof *)
Ltac representNP := match goal with [ |- @representableP ?i ?ff ?n ?G ] => let tac k := (let envBase := fresh "envBase" in (pose (@HiddenTerm (nat -> @D i) (fst k)) as envBase); representEnvPNP envBase (snd k)) in constructEnvCont tac end.
(*Ltac representNP := let envBase := fresh "envBase" in let envTerm := fresh "envTerm" in constructEnv' envBase envTerm; representEnvPNP envBase envTerm.*)


Ltac representEnvPPP env env2:= 
match goal with [ |- @representableP ?i ?ff ?n ?G ] => 
  let rep := fresh "rep" in let prf := fresh "prf" in let k y := (destruct y as [rep prf]) in
  (*pose ((match env1 with None => @emptyEnv i | Some kk => kk end)) as env;*)
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmQuote ff) (fun qff => 
                         monad_utils.bind (tmInferInstance None (tarski_reflector_extensions i)) (fun treO => let tre := match treO with my_Some kk => kk | my_None => defaultExtensions i end in
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t (@findPropRepresentation i tre tct FUEL qff g n qe env2)) (fun '(tPq,pPq) => 
                         monad_utils.ret (tPq,pPq)))))))) k)
  ;exists rep;exists env;exact prf 
end.
