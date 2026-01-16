open Types
open Clause
open Utils
  
(** Clause generation helper *)

(** Removal of all may-fail terms:
  
  A may fail term may only occur at top level in three predicates:
    - att(u)
    - attBin(u,v)
    - attGuess(u,v)
  Note that attGuess and attBin behave typically the same way. 
  Constraints never contain may-fail variables. (They have been removed
  from constraints of destructor rules by [Terms.generate_destructor_with_side_cond].)

  When working on non-interference properties, fail and the may-fail variables may also appear in testunif predicates, at the top, plus possibly inside a tuple.
  In such a test, the may-fail terms appear only in clauses for destructor function symbols:
    testunif((v1,...,vn),EVar(N1,...,Nn)) && att(v1) && ... && att(vn) ==> bad
  In that clause, all v1,...,vn are may-fail variables. So when simplifying the clauses, 
    if Ni is not a may-fail term then vi will be instantiated by Ni.
    if Ni is fail then vi will be instantiated by Ni
    if Ni is a may-fail variable then it will only be unified with vi. Another Nj may be equal 
      to Ni  
  Hence, we can: 
    - Replace each vi with fail if Ni is a may-fail term and otherwise replace vi with a classical variable.
      (The case of several Ni that are the same may-fail variable and vi is a classical variable is subsumed
      by the clause att(x) && att(y) && testunif(x,y) -> bad.) 
    - In the testunif predicate, we remove the fail component.

  We consider the following 4 rules:
  1- If H -> att(u) then we can instantiate u with a classic variable x as instantiating u with fail
    would be subsumed by the clause -> att(fail)
     If H -> attBin(fail,u), then can instantiate u with a classic variable x as instantiating u with fail
    would be subsumed by the clause -> attBin(fail,fail). We have the symmetrical case + the two cases with attGuess.
  2- If R = attBin(fail,v) && H -> C and R is not the clause Rfail = (attBin(fail,x) -> bad) then v = fail.
    Indeed, if v <> fail then it would be subsumed by Rfail. We have the symmetrical case + the two cases with attGuess.
     If R = attBin(fail,M) && H -> C where M is not fail nor a may-fail variable
     and R is not the clause Rfail = (attBin(fail,x) -> bad) then 
     remove the clause (it is subsumed by Rfail).
  3- If R = attBin(M,v) && H -> C where M is not fail nor a may-fail variable and 
    R is not the clause Rfail = (attBin(x,fail) -> bad) then v = y with y a fresh variable
    Indeed, if v = fail then it would be subsumed by Rfail. We have the symmetrical case + the two cases with attGuess.
  4- If H -> attBin(u,v) then we can instantiate in three possibilities (x,y), (x,fail), (fail,y)
     If H -> attBin(M,v) then we can instantiate v in two possibilities y or fail.
     We have the symmetrical case + the cases with attGuess.

  Procedure: 
    0) In case of non-interference, simplify testunif as outlined above.
    1) Apply the first three rules as long as we can.
    2) If C contains may-fail variables, apply rule 4 and restart 
       (when the result is (M,fail) or (fail,M), remove_fail_facts will replace it by bad)
    3) If C does not contain may-fail variables then remove_fail_facts will
       remove all facts containing may-fail variables.
       (because the remaining hypotheses that contain may-fail variables can only be
       att(u), attBin(u,v), attGuess(u,v) and these facts are satisfiable)

  The instantiation of variables and removal of hypotheses are done separately,
  because the instantiation does not modify the history, so it can be done 
  before the display of the initial clauses, while the removal of hypotheses and
  replacement of (M,fail) and (fail,M) conclusions with bad lead to a modification
  of history as if resolution had been done, so we perform it after displaying the
  initial clauses.
*)

let rec status_term = function
  | Var { link = TLink t; _ } -> status_term t
  | FunApp(f,[]) when f.f_cat = Failure -> 0
  | Var(v) when v.unfailing -> 1
  | _ -> 2

let inst_fail_fail f_next ty t1 t2 =
  try
    let fail = Terms.get_fail_term ty in
    Terms.auto_cleanup_save (fun () ->
      Terms.unify t1 fail;
      Terms.unify t2 fail;
      f_next ()
    )
  with Terms.Unify -> ()

let inst_fail_x f_next ty t1 t2 =
  try
    Terms.auto_cleanup_save (fun () ->
      Terms.unify t1 (Terms.get_fail_term ty);
      Terms.unify t2 (Terms.new_var_def_term ty);
      f_next ()
    )
  with Terms.Unify -> ()

let inst_x_y f_next ty t1 t2 =
  try
    Terms.auto_cleanup_save (fun () ->
      Terms.unify t1 (Terms.new_var_def_term ty);
      Terms.unify t2 (Terms.new_var_def_term ty);
      f_next ()
    )
  with Terms.Unify -> ()

let instantiate_may_fail_in_hyp f_next f_next_repeat hypl =

  let rec instantiate_hyp = function
    | [] -> f_next ()
    | Pred({p_info = AttackerBin(_,ty) | AttackerGuess(ty);_},[t1; t2]):: q ->
        begin match status_term t1, status_term t2 with
        | 0,2 | 2,0 -> 
            (* Remove clause *)
            ()
        | 0,1 | 1,0 -> 
            (* Unify with fact fail-fail *)
            inst_fail_fail f_next_repeat ty t1 t2
        | 1,2 | 2,1 -> 
            (* Unify with fact x,y *)
            inst_x_y f_next_repeat ty t1 t2
        | _ -> 
            (* Don't do anything *)
            instantiate_hyp q
        end
    | f::q -> 
        (* Don't do anything *)
        instantiate_hyp q
  in

  instantiate_hyp hypl
  
let instantiate_may_fail_in_concl case_analysis f_next f_next_repeat = function
  | Pred({p_info = AttackerBin(_,ty) | AttackerGuess ty; _},[t1;t2]) ->
      begin match status_term t1, status_term t2 with
        | 0, 0 -> 
            (* fail, fail *)
            f_next ()
        | 0, 1 -> 
            (* fail, may-fail *)
            inst_fail_x f_next ty t1 t2
        | 1, 0 -> 
            (* may-fail, fail *)
            inst_fail_x f_next ty t2 t1
        | 1, 1 when case_analysis -> (* This is the case analysis. It is done later. *)
            inst_fail_x f_next_repeat ty t1 t2;
            inst_fail_x f_next_repeat ty t2 t1;
            inst_x_y f_next_repeat ty t1 t2
        | 1, 2 when case_analysis->
            inst_x_y f_next_repeat ty t1 t2;
            inst_fail_x f_next_repeat ty t1 t2;
        | 2, 1 when case_analysis->
            inst_x_y f_next_repeat ty t1 t2;
            inst_fail_x f_next_repeat ty t2 t1
        | _ -> f_next ()
        end
  | Pred({p_info = Attacker(_,ty);_}, [t]) ->
      begin match status_term t with
        | 0 -> f_next ()
        | 1 -> 
            let x = Terms.new_var_def_term ty in
            Terms.auto_cleanup_save (fun () ->
              Terms.unify x t;
              f_next ()
            )
          | _ -> f_next ()
      end
  | _ -> f_next ()

let instantiate_may_fail_in_testunif = function
  | Pred({ p_info = TestUnifP _}, [FunApp(f1,args1);FunApp(f2,args2)]) 
      when f1 == f2 &&
      List.for_all (function Var v when v.unfailing -> true | _ -> false) args1 ->

      let (args1',args2') =
        List.fold_right2 (fun t1 t2 (acc1,acc2) -> match t2 with
          | FunApp(f,[]) when f.f_cat = General_mayfail_var || f.f_cat = Failure ->
              (* May fail term *)
              Terms.unify t1 (Terms.get_fail_term (snd f.f_type));
              (acc1,acc2)
          | _ -> 
              (* Classical term *)
              Terms.unify t1 (Terms.new_var_def_term (Terms.get_term_type t2));
              (t1::acc1,t2::acc2)
        ) args1 args2 ([],[])
      in
      let thyp = List.map Terms.get_term_type args1' in
      let tuple_fun = Terms.get_tuple_fun thyp in
      let testunif_pred = Param.get_pred (TestUnifP(snd tuple_fun.f_type)) in
      Pred(testunif_pred, [ FunApp(tuple_fun, args1') ; FunApp(tuple_fun, args2')])
  | fact -> fact

let instantiate_may_fail f_next hypl concl constra tags = match tags with
  | Init 
  | Rfail _ -> f_next hypl concl constra tags
  | _ -> 
      let acc_data = ref [] in

      let copy_tags2 = function
        | ProcessRule (hypsec_l,t_l) -> ProcessRule(hypsec_l,List.map Terms.copy_term2 t_l)
        | tag -> tag
      in 

      (* Generates the new data *)
      Terms.auto_cleanup_save (fun () ->
        let hypl' = List.map instantiate_may_fail_in_testunif hypl in

        let rec apply_rules () = 
          instantiate_may_fail_in_concl false (fun () ->
            instantiate_may_fail_in_hyp (fun () ->
              instantiate_may_fail_in_concl true (fun () -> 
                acc_data := 
                  (
                    List.map Terms.copy_fact2 hypl',
                    Terms.copy_fact2 concl,
                    Terms.copy_constra2 constra,
                    copy_tags2 tags
                  ) :: !acc_data
              ) apply_rules concl
            ) apply_rules hypl'
          ) apply_rules concl
        in

        apply_rules ()
      );

      List.iter (fun (hypl,concl,constra,tags) -> f_next hypl concl constra tags) !acc_data


let remove_fail_facts get_fact f_next (hypl,concl,hist,constra) = match hist with
  | Rule(_,Rfail _,_,_,_)  -> ()
  | Rule(_,Init,_,_,_) -> 
      begin match concl with 
        | Pred({ p_info = AttackerBin _ | AttackerGuess _ | Attacker _;_}, t::_) when status_term t = 0 -> ()
        | _ -> f_next (hypl,concl,hist,constra)
      end
  | _ ->
    (* We remove facts attBin(fail,fail), attGuess(fail,fail) and att(fail)
       as well as attBin(u,v), attGuess(u,v) and att(u) from hypotheses
       These are the only possibilities for may-fail terms after
       application of [instantiate_may_fail] *)
    let (_,hist1,hypl1) = 
      List.fold_right (fun hyp (n,hist',hypl') -> match get_fact hyp with 
        | Pred(p',args') when List.exists Terms.is_may_fail_term args' ->
            let hist_fail = History.get_rule_hist (RConclFail(p')) in
            let hist'' = Resolution(hist_fail,n,hist') in
            (n-1,hist'',hypl')
        | _ -> (n-1,hist',hyp::hypl')
      ) hypl (List.length hypl - 1,hist,[])
    in
    let (hist2,concl1) = match concl with
      | Pred({ p_info = AttackerBin _ | AttackerGuess _;_} as p, [t1;t2]) ->
          begin match status_term t1, status_term t2 with
            | 0,2 ->
                let hist_fail = History.get_rule_hist (RFail(false,p)) in
                let hist' = Resolution(hist1,0,hist_fail) in
                (hist',Pred(Param.bad_pred,[]))
            | 2,0 ->
                let hist_fail = History.get_rule_hist (RFail(true,p)) in
                let hist' = Resolution(hist1,0,hist_fail) in
                (hist',Pred(Param.bad_pred,[]))
            | _ -> (hist1,concl)
          end
      | _ -> (hist1,concl)
    in

    f_next (hypl1,concl1,hist2,constra)

(* Transformation from reduction to clauses *)

let clauseOrd_of_reduction f_next (hypl,concl,hist,constra) = 
  let hypl' = match hist,hypl,concl with
    (* Rechability and equivalence *)
    | Rule(_,Rl _,_,_,_), [mess_fact;att_fact],_ -> [(mess_fact,COSpecific [1,Leq],0);(att_fact,COSpecific [1,Less],0)]
    (* Equivalence *)
    | Rule(_,Apply _,_,_,_), _, Pred({ p_info = AttackerBin _ | AttackerGuess _; _},[t1;t2]) when Terms.is_may_fail_term t1 || Terms.is_may_fail_term t2 ->
        List.map (fun f -> f,COSpecific [1,Leq],0) hypl
    | Rule(_,Rfail _,_,_,_), _, _
    | Rule(_,TestComm _,_,_,_),_,_ 
    | Rule(_,TestEq _,_,_,_),_,_ 
    | Rule(_,Ri _,_,_,_),_,_
    | Rule(_,Ro _,_,_,_),_,_ ->  
        List.map (fun f -> f,COSpecific [1,Leq],0) hypl
    (* Others *)
    | _ ->
        List.map (fun fact -> 
          if Ordering.can_hyp_and_concl_be_ordered fact concl
          then
            if Ordering.is_pred_to_prove_fact (Terms.unblock_predicate_fact fact)
            then (fact,COSpecific [1,Less],0)
            else (fact,COSpecific [1,Leq],0)
          else (fact,CONone,0)
        ) hypl
  in
  remove_fail_facts (fun (f,_,_) -> f) (fun (hypl,concl,hist,constra) ->
    f_next 
    { 
      Ord.hypotheses = hypl;
      Ord.conclusion = concl;
      Ord.history = hist;
      Ord.constraints = constra
    }
  ) (hypl',concl,hist,constra)

let clause_of_reduction f_next =
  remove_fail_facts (fun f -> f) (fun (hypl,concl,hist,constra) ->
    f_next 
    { 
      Std.hypotheses = hypl;
      Std.conclusion = concl;
      Std.history = hist;
      Std.constraints = constra
    }
  )

let remove_subsumed_attacker_clauses_before_display red_rules nrule =
  if !Param.remove_subsumed_clauses_before_display then
    begin
      Database.FeatureGenClause.initialize ();
      let tmp_rules = Database.SetClause.create () in
      (* Store in tmp_rules the rules after removing subsumed rules and tautologies *)
      List.iter (function (hyp, concl, hist, constra)->
        (* eliminate tautologies *)
        if List.exists (Terms.equal_facts concl) hyp then () else
        (* eliminate subsumed clauses *)
        (* TODO : This will need to be changed when working on hash cons term where we cannot have subsumption with may-fail terms. *)
        let annot_rule = Database.FeatureGenClause.generate_feature_vector_and_subsumption_data { Std.hypotheses = hyp; Std.conclusion = concl; Std.history = hist; Std.constraints = constra } in

        if Database.SetClause.implies tmp_rules annot_rule
        then ()
        else
          begin
            Database.SetClause.deactivate_implied_by () tmp_rules annot_rule;
            (* Saying that the conclusion is the selected fact does not impact the subsumption. *)
            Database.SetClause.add tmp_rules annot_rule None ()
          end
      ) !red_rules;
      (* Renumber the rules *)
      red_rules := [];
      nrule := 0;
      Database.SetClause.iter (fun elt ->
        match elt.annot_clause with
        | { history = Rule(_, tags, hyp, concl, constra); _} as cl,_ ->
            red_rules := (cl.hypotheses, cl.conclusion, Rule(!nrule, tags, hyp, concl, constra), cl.constraints) :: (!red_rules);
            incr nrule
        | _ -> Parsing_helper.internal_error __POS__ "[transl_helper.remove_subsumved_attacker_clauses_before_display] All clauses should have history Rule(...) at this point"
      ) tmp_rules
    end

(** Membership predicates *)

let check_membership ext memberOptim hypl constra concl =
  let update p f = 
    memberOptim :=
      Utils.List.replace_assq (fun _ -> function
        | None -> Some f
        | Some f' when f == f' -> Some f' 
        | Some f' -> 
            Parsing_helper.input_error ("The predicate "^p.p_name^" has been declared with option memberOptim but has two function symbols as set constructor: "^(Display.string_of_fsymb f')^" and "^(Display.string_of_fsymb f)^".") ext
      ) p !memberOptim
  in

  let Pred(p,_) = concl in
  if List.mem_assq p !memberOptim
  then
    match hypl, concl with 
    | [Pred(p,[Var x; Var y])], Pred(p',[Var x'; FunApp(f,[Var x'';Var y'])]) when 
      p == p' && x == x' && y == y' && Terms.is_true_constraints constra -> update p f
    | [], Pred(p,[Var x; FunApp(f,[Var x';Var y])]) when 
        x == x' && Terms.is_true_constraints constra -> update p f
    | _ ->
	Parsing_helper.input_error ("The predicate "^p.p_name^" has been declared with option memberOptim but a clause is given that does not correspond to the expected membership clauses.") ext

let forbid_equiv_membership ext memberOptim hypl concl =
  try 
    let Pred(p,_) =  List.find (function Pred(p,_) -> List.mem_assq p !memberOptim) (concl::hypl) in
    Parsing_helper.input_error ("The predicate "^p.p_name^" has been declared with option memberOptim but a <=> clause is given for this predicate, which does not correspond to the expected membership clauses.") ext
  with Not_found -> ()
      
let find_init_membership p f (rules:reduction list) = 
  let f_map = function
    | [], Pred(p',[Var x; FunApp(f',[Var x';Var y])]), hist, constra when 
      x == x' && f == f' && p == p' && Terms.is_true_constraints constra -> Some hist
    | _ -> None
  in
  match List.find_map f_map rules with
    | Some hist -> hist
    | None -> Parsing_helper.user_error  ("The predicate "^p.p_name^" has been declared with option memberOptim but the initial membership clause is not given.")

let find_rec_membership p f (rules:reduction list) = 
  let f_map = function
    | [Pred(p',[Var x;Var y])], Pred(p'',[Var x'; FunApp(f',[Var x'';Var y'])]), hist, constra when 
      x == x' && y == y' && f == f' && p == p' && p == p'' && Terms.is_true_constraints constra -> Some hist
    | _ -> None
  in
  match List.find_map f_map rules with
    | Some hist -> hist
    | None -> Parsing_helper.user_error  ("The predicate "^p.p_name^" has been declared with option memberOptim but the recursive membership clause is not given.")

let set_membership_predicates rules =
  List.map (function 
    | p, Some f -> p,(find_init_membership p f rules, find_rec_membership p f rules, f)
    | p, _ -> Parsing_helper.user_error  ("The predicate "^p.p_name^" has been declared with option memberOptim but no membership clause is given.")
  ) 
