open Types
open Terms

(* Equality *)

let rec equal_terms_with_links t1 t2 = (t1 == t2) || (match (t1,t2) with
  | Var v, _ ->
      begin match Terms.get_link v with 
      | TLink t -> equal_terms_with_links t t2
      | VLink v -> equal_terms_with_links (Var v) t2
      | _ ->
        match t2 with
        | Var v' ->
            begin match Terms.get_link v' with 
            | TLink t' -> equal_terms_with_links t1 t'
            | VLink v' -> equal_terms_with_links t1 (Var v')
            | _ -> v == v'
            end
        | _ -> false
      end
  | _, Var v' ->
      begin match Terms.get_link v' with 
      | TLink t' -> equal_terms_with_links t1 t'
      | VLink v' -> equal_terms_with_links t1 (Var v')
      | _ -> false
      end
  | FunApp(f,l),FunApp(f',l') -> (f == f') && (List.for_all2 equal_terms_with_links l l')
  )

let equal_facts_with_links f f' = (f == f') || (match (f,f') with
  Pred(p,l), Pred(p',l') -> (p == p') && (List.for_all2 equal_terms_with_links l l'))

let rec equal_closed_terms t1 t2 = match (t1,t2) with
  Var v, t' ->
    begin
      match Terms.get_link v with
	TLink t -> equal_closed_terms t t'
      |	_ -> Parsing_helper.internal_error __POS__ "unexpected link in equal_closed_terms (reduction.ml)"
    end
| t, Var v' ->
    begin
      match Terms.get_link v' with
	TLink t' -> equal_closed_terms t t'
      |	_ -> Parsing_helper.internal_error __POS__ "unexpected link in equal_closed_terms (reduction.ml)"
    end
| FunApp(f,l),FunApp(f',l') ->
   (f == f') && (List.for_all2 equal_closed_terms l l')

let equal_closed_facts f1 f2 = match f1, f2 with
  | Pred(p1,args1), Pred(p2,args2) ->
      p1 == p2 && List.for_all2 equal_closed_terms args1 args2

let equal_tags t1 t2 =
  match (t1,t2) with
    ProcessRule(h1, tl1), ProcessRule(h2,tl2) ->
      (List.length h1 == List.length h2) && (List.for_all2 (=) h1 h2) &&
      (List.length tl1 == List.length tl2) &&
      (List.for_all2 equal_terms_with_links tl1 tl2)
  | Apply(f1,p1), Apply(f2,p2) -> (f1 == f2) && (p1 == p2)
  | TestApply(f1,p1), TestApply(f2,p2) -> (f1 == f2) && (p1 == p2)
  | TestEq p1, TestEq p2 -> p1 == p2
  | Rl(p1,p1'), Rl(p2,p2') -> p1 == p2 && p1' == p2'
  | Rs(p1,p1'), Rs(p2,p2') -> p1 == p2 && p1' == p2'
  | Ri(p1,p1'), Ri(p2,p2') -> p1 == p2 && p1' == p2'
  | Ro(p1,p1'), Ro(p2,p2') -> p1 == p2 && p1' == p2'
  | TestComm(p1,p1'), TestComm(p2,p2') -> p1 == p2 && p1' == p2'
  | LblEquiv, LblEquiv -> true
  | LblClause, LblClause -> true
  | LblEq, LblEq -> true
  | WeakSecr, WeakSecr -> true
  | Rn p1, Rn p2 -> p1 == p2
  | Init, Init -> true
  | PhaseChange, PhaseChange -> true
  | TblPhaseChange, TblPhaseChange -> true
  | LblComp, LblComp -> true
  | LblNone, LblNone -> true
  | TestUnif, TestUnif -> true
  | _ -> false

let equal_constra c1 c2 =
  List.length c1.neq == List.length c2.neq &&
  List.length c1.is_nat == List.length c2.is_nat &&
  List.length c1.is_not_nat == List.length c2.is_not_nat &&
  List.length c1.geq == List.length c2.geq &&

  List.for_all2 (fun l1 l2 ->
    List.length l1 == List.length l2 &&
    List.for_all2 (fun (t1,t1') (t2,t2') ->
      equal_terms_with_links t1 t2 &&
      equal_terms_with_links t1' t2'
    ) l1 l2
  ) c1.neq c2.neq &&

  List.for_all2 equal_terms_with_links c1.is_nat c2.is_nat &&
  List.for_all2 equal_terms_with_links c1.is_not_nat c2.is_not_nat &&
  List.for_all2 (fun (t1,n1,t1') (t2,n2,t2') ->
    n1 == n2 &&
    equal_terms_with_links t1 t2 &&
    equal_terms_with_links t1' t2'
  ) c1.geq c2.geq

(* Matching *)

let rec match_terms t1 t2 =
  if not (Param.get_ignore_types()) then
    if (get_term_type t1 != get_term_type t2) then
      assert false;
  match (t1,t2) with
  | _, Var v' -> 
      begin match Terms.get_link v' with 
      | TLink t2' -> match_terms t1 t2'
      | _ -> Parsing_helper.internal_error __POS__ "Bad link in match_terms (1)"
      end
  | Var v1, _ -> 
      begin match Terms.get_link v1 with 
      | TLink t1' -> match_terms t1' t2
      | NoLink -> 
          if v1.unfailing
          then link v1 (TLink t2)
          else
            begin match t2 with
            | FunApp(f_symb,_) when f_symb.f_cat = Failure -> raise Unify
            | _ -> link v1 (TLink t2)
            end
      | _ -> Parsing_helper.internal_error __POS__ "Bad link in match_terms (2)"
      end
   | FunApp(f1,l1'), FunApp(f2,l2') ->
        if f1 != f2 then raise Unify;
        List.iter2 match_terms l1' l2'

(* Retrieve variables *)

let rec get_vars vars = function
  | Var v -> 
      begin match Terms.get_link v with
      | TLink t -> get_vars vars t
      | _ -> 
          if not (List.memq v !vars)
          then vars := v :: !vars
      end
  | FunApp(_,args) -> List.iter (get_vars vars) args

(* Test whether a term has a variable *)
let rec has_vars = function
  | Var v ->
      begin match Terms.get_link v with
        | NoLink -> true
        | TLink t -> has_vars t
        | _ -> Parsing_helper.internal_error __POS__ "[Termslinks.has_vars] Unexpected link"
      end
  | FunApp(_,args) -> List.exists has_vars args
