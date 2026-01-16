
open Types
open Terms
open Clause
open Utils

(* Global variables. *)

let sound_mode = ref false
let is_inside_query = ref false
let is_equivalence_query = ref false
let initialized = ref false
let close_with_equations = ref false

let ordered_saturation = ref false
let predicates_for_second_saturation = ref []
let events_for_second_saturation = ref []

let equiv_set = ref ([]: (fact list * fact * history array) list)
let not_set = ref ([]: fact list)
let elimtrue_set = ref ([]: (history * fact) list)
let events_only_for_lemmas = ref []
let events_only_for_lemmas_without_options = ref []
let all_original_lemmas = ref []

let memberOptim_set = ref []

(** Initialization of the user defined predicates clauses defined with <-> or <=> *)

(** We check that in an equivalence F1 && ... && Fn <-> F the terms F1\sigma,...,Fn\sigma are all smaller
    than F\sigma for all substitutions \sigma. This is done by showing that the multiset of variables of
    Fk is included in the one of F and that the size of Fk is smaller than the size of F. *)

let rec get_vars_rep vlist = function
  | Var v -> vlist := v :: (!vlist)
  | FunApp(_,l) -> List.iter (get_vars_rep vlist) l

let get_vars_rep_fact vlist = function
  | Pred(p,l) -> List.iter (get_vars_rep vlist) l

(** [remove_first vlist v] removes the first occurrence of [v] in [vlist]. 
   @raise Not_found when [v] does not occur in [vlist] *)
let remove_first vlist v =
  let rec remove_first_rec v = function
    | [] -> raise Not_found
    | v'::l -> if v' == v then l else v' :: (remove_first_rec v l)
  in
  vlist := remove_first_rec v (!vlist)

let is_smaller f1 f2 =
  (Terms.fact_size f1 < Terms.fact_size f2) &&
  (let v1 = ref [] in
  let v2 = ref [] in
  get_vars_rep_fact v1 f1;
  get_vars_rep_fact v2 f2;
  try
    List.iter (remove_first v2) !v1;
    true
  with Not_found ->
    false)

let check_equiv (hyp, concl, n) =
  (* Check that \sigma h smaller than \sigma concl for all \sigma, for all h in hyp.
     This implies termination of the replacement process *)
  if not (List.for_all (fun h -> is_smaller h concl) hyp) then
    Parsing_helper.user_error "For equivalences, the conclusion must be larger than the hypotheses\nand this must be true for all instances of these facts.";
  (* Check that only ONE replacement rule applies to a given fact.
     This implies confluence of the replacement process *)
  List.iter (fun (_, concl',_) ->
    try
      Terms.auto_cleanup (fun () -> Terms.unify_facts concl concl');
      Parsing_helper.user_error "Conflict between equivalences: two of them apply to the same fact.";
    with Unify -> ()
        ) (!equiv_set);
  match concl with
    Pred(p,((FunApp(f,_) :: _) as l)) when
         p.p_prop land Param.pred_TUPLE != 0 &&
           f.f_cat = Tuple ->
     begin
       try
         let _ = reorganize_fun_app f l in
         Parsing_helper.user_error "Conflict between an equivalence and the decomposition of data constructors:\nan equivalence applies to a fact which is also decomposable by data constructors."
       with Not_found -> ()
     end
  | _ -> ()

(** Generation of history rules*)
let generate_history_rule set =
  List.map (fun (hypl,concl,n) ->
    let hist_array = Array.make (List.length hypl + 1) (Empty Param.dummy_fact) in
    
    (* History of the rule F1 && ... && Fn -> F *)
    hist_array.(0) <- Rule(n, LblEquiv, hypl, concl, true_constraints);

    (* History of the rules F -> Fk*)
    List.iteri (fun i fact ->
      hist_array.(i+1) <- Rule(n+i+1,LblEquiv,[concl],fact, true_constraints)
    ) hypl;

    (hypl,concl,hist_array)
  ) set

let initialize_equiv_set set =
  (* Verify that the rules are ok *)
  List.iter check_equiv set;
  (* Store the replacement rules *)
  equiv_set := generate_history_rule set

(* Initialise Simplification for useless events *)

let initialise_useless_events_for_lemmas events_in_queries lemmas =
  events_only_for_lemmas := [];
  events_only_for_lemmas_without_options := [];
  all_original_lemmas := [];

  (* We record first the lemmas that are used in either saturation or solving *)
  List.iter (fun lem ->
    if lem.l_sat_app || lem.l_verif_app
    then all_original_lemmas := lem :: !all_original_lemmas
  ) lemmas;

  (* We first add to [events_in_queries] the events of the lemmas with the option REKeep. *)
  let acc_events_in_queries = ref events_in_queries in

  List.iter (fun lemma ->
    if lemma.l_remove_events = REKeep
    then
      List.iter (function
        | Pred(p,(FunApp(ev,_)::_)) when p == Param.event_pred || p == Param.event2_pred ->
            if not (List.memq ev !acc_events_in_queries)
            then acc_events_in_queries := ev :: !acc_events_in_queries
        | _ -> ()
      ) lemma.l_premise
  ) !all_original_lemmas;

  List.iter (fun lemma ->
    if lemma.l_remove_events = RERemove || (lemma.l_remove_events = RENone && !Param.event_lemma_simplification)
    then
      List.iter (function
        | Pred(p,(FunApp(ev,_)::_)) when p == Param.event_pred || p == Param.event2_pred ->
            if not (List.memq ev !acc_events_in_queries) && not (List.memq ev !events_only_for_lemmas)
            then events_only_for_lemmas := ev :: !events_only_for_lemmas
        | _ -> ()
      ) lemma.l_premise
  ) !all_original_lemmas;

  List.iter (fun lemma ->
    List.iter (function
      | Pred(p,(FunApp(ev,_)::_)) when p == Param.event_pred || p == Param.event2_pred ->
          if not (List.memq ev events_in_queries) && not (List.memq ev !events_only_for_lemmas_without_options)
          then events_only_for_lemmas_without_options := ev :: !events_only_for_lemmas_without_options
      | _ -> ()
    ) lemma.l_premise
  ) !all_original_lemmas

(** The simplification rules module *)

module MakeSimplificationRules
  (H:HypSig)
  (C:ClauseSig with type hyp = H.hyp) 
  (S:Selfun.SelfunSig with type clause = C.clause)
  (W:Weaksecr.WeakSecrSig with type clause = C.clause)
  (N:Noninterf.NonInterfSig with type clause = C.clause)
  (Sub:Database.SubsumptionSig with type clause = C.clause and type hyp = H.hyp)
  (Set:Database.SetSig with type hyp = H.hyp and type clause = C.clause and type subsumption_data = Sub.subsumption_data)
  (Q:Database.QueueSig with type clause = C.clause and type subsumption_data = Sub.subsumption_data)
  (DB:Database.DBSig with type clause = C.clause and type 'a set = 'a Set.t and type queue = Q.t) =
struct

  open C

  (* 1 - Limits the number of hypotheses
     Disabled in sound mode *)

  let limit_length_constraints n c =
    {
      is_nat = Utils.List.crop n c.is_nat;
      neq = List.map (Utils.List.crop n) (Utils.List.crop n c.neq);
      is_not_nat = Utils.List.crop n c.is_not_nat;
      geq = Utils.List.crop n c.geq
    }

  let rec limit_length_history n maxn h = 
    if maxn <= n
    then h
    else limit_length_history n (maxn - 1) (HRemovedBySimplification(n,h))

  let limit_length cl = 
    if !sound_mode then cl else
    let max_hyp = !Param.max_hyp in
    if max_hyp < 0 then cl else
    { cl with
      hypotheses = Utils.List.crop max_hyp cl.hypotheses;
      constraints = limit_length_constraints max_hyp cl.constraints;
      history = limit_length_history max_hyp (List.length cl.hypotheses) cl.history
    }

  (* 2 - Limits the depth of terms
     Terms deeper than !Param.max_depth are replaced with variables.
     Disabled in sound mode *)

  let rec limit_depth_term n = function
    | Var _ as t -> t 
    | FunApp(f,args) ->
        if n = 0
        then Terms.new_var_def_term (snd f.f_type)
        else FunApp(f, List.map (limit_depth_term (n-1)) args)

  let limit_depth_fact n = function
    | Pred(p,args) -> Pred(p,List.map (limit_depth_term n) args) 

  let limit_depth cl = 
    if !sound_mode then cl else
    let max_depth = !Param.max_depth in
    if max_depth < 0 then cl else
    (* Cannot limit depth to less than 2 to make sure that occurrences
       of events are preserved. Avoids 
       File "proverif/src/piauth.ml", line 504
       Internal error: [generate_constra_occ] Should always be names. *)
    let max_depth = if max_depth <= 2 then 2 else max_depth in
    { cl with 
      hypotheses = List.map (H.map_fact (limit_depth_fact max_depth)) cl.hypotheses;
      conclusion = limit_depth_fact max_depth cl.conclusion;
      constraints = Terms.map_constraints (limit_depth_term max_depth) cl.constraints
    }

  (* 3 - Conditional removal of hypotheses.
    It replaces the previous removal of hypotheses related to 
    induction. *)

  
  (* 4 - Decompose tuples and data constructors in hypotheses of rules. *)

  (* It is important for the correctness of this optimization that
    p:x is never selected when p is a predicate on which we
    perform the decomposition of data constructors, except
    when there are only such facts in the clause.

    Also eliminates duplicate hypotheses. 
    
    Warning: The clause should not contain links. *)

  let hist_is_exempt_from_data_simplify h =
    match h with
    | Rule (_,Apply(f,_),_,_,_) -> Terms.is_data_or_proj f
    | Rule (_,LblEquiv,_,_,_) -> true
    | _ -> false
  
  let rec decompose_hyp_rec accu hypl =
    List.fold_right (fun hyp1 (hypl,nl,histl) ->
      let default() = match Utils.List.find_and_replace (H.equal_facts hyp1) (H.merge hyp1) hypl with
        | None -> (hyp1::hypl, nl-1, histl)
        | Some(idx,hypl') -> (hypl', nl-1, Removed(nl, idx+nl+1, histl))
      in
      match H.get_fact hyp1 with
        | Pred(chann,_) when chann == Param.event_pred_block || chann == Param.inj_event_pred_block || chann == Param.event2_pred_block -> default ()
        | Pred(chann,l0) ->
          let rec try_equiv_set = function
              [] ->
                if chann.p_prop land Param.pred_TUPLE != 0 then
                  try
                    match l0 with
                      (FunApp(f,_) :: _) when f.f_cat = Tuple ->
                        let l = reorganize_fun_app f l0 in
                        begin match History.get_rule_hist (RApplyFunc(f,chann)) with
                          | Rule(_, _, hyp, _, _) as hist_dec ->
                              decompose_hyp_rec (hypl, nl+(List.length l)-1, (Resolution(hist_dec, nl, histl)))
                                (List.map2 (fun (Pred(p',_)) x -> H.create_strictly_before (Pred(p', x)) hyp1) hyp l)
                          | _ -> Parsing_helper.internal_error __POS__ "[Rules.decompose_hyp_rec] Unexpected history."
                        end
                    | _ -> default()
                  with Not_found -> default()
                else default()
            | (hypeq, concleq, hist_array)::l ->
                try
                  let hypeq' =
                    Terms.auto_cleanup (fun () ->
                      Terms.match_facts concleq (H.get_fact hyp1);
                      List.map (fun fact -> 
                        H.create_strictly_before (Terms.copy_fact3 fact) hyp1
                      ) hypeq
                    )
                  in
                  let hist_dec = hist_array.(0) in
                  decompose_hyp_rec (hypl, nl+(List.length hypeq')-1, (Resolution(hist_dec, nl, histl))) hypeq'
                with NoMatch ->
                  try_equiv_set l
          in
          try_equiv_set (!equiv_set)
        ) hypl accu
  
  let decompose_hyp_tuples cl =
    if hist_is_exempt_from_data_simplify cl.history  then
      cl
    else
      let (hypl', _, histl') =
        decompose_hyp_rec ([], (List.length cl.hypotheses)-1, cl.history) cl.hypotheses
      in
      { cl with
        hypotheses = hypl';
        history = histl'
      }
  

  let decompose_hyp_tuples_rule next_stage cl =
    next_stage (decompose_hyp_tuples cl)

  (* 5 - Eliminate hypotheses p(x1...xn) where p has been declared "elimVar"
    or "elimVarStrict" and x1...xn do not occur elsewhere.
    Such a declaration means that p(x...x) is true for some value of x.
    This is correct in particular when p = attacker. When p is declared
    elimVar and we are not in sound_mode, x1...xn are allowed to occur
    in inequalities.

    In sound_mode, we always require that x1...xn do not occur in
    inequalities. *)

  let fold_right_prev3 f l_vars l_hyp acc =
    let rec fold_aux prev_vars l_vars l_hyp = match l_vars, l_hyp with
      | [],[] -> acc
      | vars::q_vars, t::q ->
          let acc' = fold_aux (vars::prev_vars) q_vars q in
          f prev_vars vars q_vars t acc'
      | _ -> Parsing_helper.internal_error __POS__ "[Rules.fold_right_prev] Lists should be of same size"
    in
    fold_aux [] l_vars l_hyp
  
  let elim_any_x_condition chann l concl_vars prev_vars next_vars constra_vars =
    (
      chann.p_prop land Param.pred_ANY != 0 &&
      (* We first check that all terms are variables *)
      List.for_all (function Var _ -> true | _ -> false) l &&
      (* We now check the occurrences (costly) *)
      List.for_all (function
        | Var v ->
            not (
              (!sound_mode && List.memq v (Lazy.force constra_vars)) ||
              List.memq v (Lazy.force concl_vars) ||
              List.exists (fun fv -> List.memq v (Lazy.force fv)) next_vars ||
              List.exists (fun fv -> List.memq v (Lazy.force fv)) prev_vars
            )
        | _ -> false
      ) l
    )
    ||
    (
      chann.p_prop land Param.pred_ANY_STRICT != 0 &&
      (* We first check that all terms are variables *)
      List.for_all (function Var _ -> true | _ -> false) l &&
      (* We now check the occurrences (costly) *)
      List.for_all (function
        | Var v ->
            not (
              List.memq v (Lazy.force constra_vars) ||
              List.memq v (Lazy.force concl_vars) ||
              List.exists (fun fv -> List.memq v (Lazy.force fv)) next_vars ||
              List.exists (fun fv -> List.memq v (Lazy.force fv)) prev_vars
            )
        | _ -> false) l
    )
  
  let elim_any_x_all cl =
  
    (* We retrieve the variables of each fact and of constraints, to avoid recomputing
       them later in the function List.find. *)
  
    let concl_vars = lazy (Terms.get_vars_fact cl.conclusion) in
    let hypl_vars = List.map (fun hyp -> lazy(Terms.get_vars_fact (H.get_fact hyp))) cl.hypotheses in
    let constra_vars = lazy(Terms.get_vars_constra cl.constraints) in
  
    let (hypl', _, hist') =
      (* [prev_vars] is the list of variable lists of the hypotheses before [hyp1] in [hypl']
         [next_vars] is the list of variable lists of the hypotheses after [hyp1] in [hypl']
         [curr_vars] is the list of variable in [hyp1].
      *)
      fold_right_prev3 (fun prev_vars curr_vars next_vars hyp1 (hypl, nl, histl) -> match H.get_fact hyp1 with
        | Pred(chann, l) as hyp_fact ->
            begin
              try
                let (hist_r, ff) =
                  List.find (fun (_, ff) ->
                    try
                      Terms.auto_cleanup (fun () ->
                        Terms.unify_facts ff hyp_fact;
                        (* check that all modified variables of hyp1 do not
                           occur in the rest of R including inequalities *)
                        List.iter (function
                          | { link = NoLink; _ } -> ()
                          | v ->
                              if
                                List.memq v (Lazy.force constra_vars) ||
                                List.memq v (Lazy.force concl_vars) ||
                                List.exists (fun fv -> List.memq v (Lazy.force fv)) next_vars ||
                                List.exists (fun fv -> List.memq v (Lazy.force fv)) prev_vars
                              then raise Unify
                        ) (Lazy.force curr_vars);
                        (* all checks successful *)
                        true
                      )
                    with Unify -> false
                  ) !elimtrue_set
                in
                (hypl, nl-1, (Resolution(hist_r, nl, histl)))
              with Not_found ->
                if elim_any_x_condition chann l concl_vars prev_vars next_vars constra_vars
                then (hypl, nl-1, (Any(nl, histl)))
                else (hyp1 :: hypl, nl-1, histl)
            end
      ) hypl_vars cl.hypotheses ([], (List.length cl.hypotheses)-1, cl.history)
    in
    { cl with
      hypotheses = hypl';
      history = hist'
    }
  
  let elim_any_x_empty_elim_set cl =
    if
      (* We apply a first test to avoid computing the variables of the clauses when not necessary *)
      List.exists (fun hyp -> match H.get_fact hyp with
        | Pred(chann,l) ->
            ((chann.p_prop land Param.pred_ANY != 0) || (chann.p_prop land Param.pred_ANY_STRICT != 0)) &&
            List.for_all (function Var v -> true | _ -> false) l
      ) cl.hypotheses
    then
      let concl_vars = lazy (Terms.get_vars_fact cl.conclusion) in
      let hypl_vars = List.map (fun hyp -> lazy (Terms.get_vars_fact (H.get_fact hyp))) cl.hypotheses in
      let constra_vars = lazy (Terms.get_vars_constra cl.constraints) in
  
      let (hypl', _, hist') =
        fold_right_prev3 (fun prev_vars _ next_vars hyp1 (hypl, nl, histl) -> match H.get_fact hyp1 with
          | Pred(chann, l) ->
              if elim_any_x_condition chann l concl_vars prev_vars next_vars constra_vars
              then (hypl, nl-1, (Any(nl, histl)))
              else (hyp1 :: hypl, nl-1, histl)
        ) hypl_vars cl.hypotheses ([], (List.length cl.hypotheses)-1, cl.history)
      in
      { cl with hypotheses = hypl'; history = hist' }
    else cl
  
  let elim_any_x r =
    if !elimtrue_set = []
    then elim_any_x_empty_elim_set r
    else elim_any_x_all r

  let elim_any_x_rule next_stage cl = 
    next_stage (elim_any_x cl)

  (* 6 - Simplify the constraints *)

  let simplify_constraints next_stage next_stage_repeat cl = 
    let get_vars () = Terms.get_vars_generic C.iter_term_exclude_constraint cl in
    
    (* We store the clause before passing them to avoid keeping some variables linked. *)
    let acc_clause = ref [] in
    let acc_clause_repeat = ref [] in

    let first_clause = ref true in

    TermsEq.simplify_constraints_optimal (Some get_vars) (fun c ->
      let cl1 = { cl with constraints = c } in
      let cl2 = 
        if !first_clause
        then (first_clause := false; cl1)
        else Terms.auto_cleanup_noexception (fun () -> C.copy cl1)
      in
      acc_clause := cl2 :: !acc_clause
    ) (fun c ->
      acc_clause_repeat := (C.copy2 { cl with constraints = c}) :: !acc_clause_repeat   
    ) cl.constraints;
    
    (* Execute the next stage *)
    List.iter next_stage !acc_clause;
    List.iter next_stage_repeat !acc_clause_repeat

  let simplify_constraints_simple cl =
    let get_vars () = Terms.get_vars_generic C.iter_term_exclude_constraint cl in
    { cl with constraints = TermsEq.simplify_constraints_simple (Some get_vars) cl.constraints }

  (* 7 - eliminate rules that have in hypothesis a "not" fact 
    (secrecy assumption) 
    
    New: We allow the application of elim_not even in the verification of the secrecy
    assumption. However, one needs to make sure that such simplification rule is 
    not applied on the initial request clause, e.g. att(u) -> att(u). *)

  let is_not_initial_request_clause cl = match cl.history with  
    | Empty _ -> false
    | _ -> true

  let elim_not next_stage cl =
    if !not_set != [] && is_not_initial_request_clause cl &&
      List.exists (fun hyp -> 
        let hyp_fact = Terms.unblock_predicate_fact (H.get_fact hyp) in
        List.exists (fun not_fact -> Terms.are_matched_facts not_fact hyp_fact) !not_set
      ) cl.hypotheses
    then ()
    else next_stage cl

  (* 8 - Eliminate tautologies (rules that conclude a fact already in their
      hypothesis).  *)

  let elim_taut next_stage cl = 
    let Pred(p_cl,args_cl) = cl.conclusion in
    
    if 
      p_cl != Param.bad_pred &&
      List.exists (fun hyp ->         
        let Pred(p_hyp,_) as hyp_fact = H.get_fact hyp in
        let Pred(unblock_p,_) as u_hyp_fact = Terms.unblock_predicate_fact hyp_fact in
        (* If the predicate [p_hyp] is not blocking, we only need to check the equality of the fact 
           Otherwise, we also have to check that the fact occured strictly before the conclusion *)
        (unblock_p == p_hyp || H.is_strictly_before_conclusion hyp) &&
	Terms.equal_facts u_hyp_fact cl.conclusion
      ) cl.hypotheses
    then ()
    else next_stage cl

  (* 9 - Decompose tuples and data constructors in conclusion
    It is important for the correctness of this optimization that
    p:x is never selected when p is a predicate on which we
    perform the decomposition of data constructors. *)

  let rec decompose_concl_data next_stage hist concl = 
    let Pred(p,args) = concl in
    if p.p_prop land Param.pred_TUPLE != 0 
    then
      match args with
      | FunApp(f,_) :: _ when f.f_cat = Tuple ->
          let l = reorganize_fun_app f args in
          List.iteri (fun n first -> match History.get_rule_hist (RApplyProj(f, n, p)) with
            | Rule(_,_,_,Pred(p',_), _) as hist_dec ->
                let concl' = Pred(p', first) in
                let hist' = Resolution(hist, 0, hist_dec) in
                decompose_concl_aux next_stage hist' concl'
            | _ -> Parsing_helper.internal_error __POS__ "[Rules.decompose_concl_tuples] Unexpected history"
          ) l
      | _ -> raise Not_found
    else raise Not_found
  
  and decompose_concl_equiv_set next_stage hist concl = function
    | [] -> decompose_concl_data next_stage hist concl
    | (hypeq, concleq, hist_array)::l ->
        try
          let hypeq' =
            Terms.auto_cleanup (fun () ->
              Terms.match_facts concleq concl;
              List.map copy_fact3 hypeq
            )
          in
          List.iteri (fun n concl' ->
            let hist_dec = hist_array.(n+1) in
            let hist' = Resolution(hist, 0, hist_dec) in
            decompose_concl_aux next_stage hist' concl'
          ) hypeq'
        with NoMatch ->
          decompose_concl_equiv_set next_stage hist concl l

  and decompose_concl_aux next_stage hist concl = 
    try 
      decompose_concl_equiv_set next_stage hist concl !equiv_set
    with Not_found -> 
      next_stage hist concl
  
  let decompose_concl_tuples next_stage cl =
    if hist_is_exempt_from_data_simplify cl.history then
      next_stage cl
    else
      let first_clause = ref true in
      decompose_concl_aux (fun hist concl ->
        let cl1 = { cl with history = hist; conclusion = concl } in

        let cl2 = 
          if !first_clause
          then (first_clause := false; cl1)
          else Terms.auto_cleanup_noexception (fun () -> C.copy cl1)
        in
        
        next_stage cl2
      ) cl.history cl.conclusion
    
  (* 10 - Element simplification 
     att(x) /\ elem(M_1, x) /\ ... /\ elem(M_n, x)
   becomes
     att(M_1) /\ ... /\ att(M_n)
   when x does not occur elsewhere in the clause.

   "att" can be any predicate declared with data decomposition (pred_TUPLE).
   The predicate "elem" must be declared pred_ELEM. *)

  (* Clauses of elem are of the form:
      -> elem(x,f(x,y))              this clause has history [init_hist]
      elem(x,y) -> elem(x,f(x',y))   this clause has history [rec_hist]
     [f] is a data constructor
  *)
  
  (* [generate_elem_hist init_hist rec_hist idx_hyp hist_origin k] with [hist_origin] being the history
    of a rule of the form 
        H && elem(t_k,x) && H' -> C 
    with |H| = idx_hyp and x = f(t_1,...,f(t_2,f(t_k,z))...).
    The function returns the history of the rule H && H' -> C 
  *)
  let generate_elem_hist init_hist rec_hist idx_hyp hist_origin k =
    let rec build hist = function
      | 1 -> Resolution(init_hist,idx_hyp,hist) 
      | k -> build (Resolution(rec_hist,idx_hyp,hist)) (k-1)
    in
    build hist_origin k
  
  (* [generate_tuple_hist apply_hist idx_hyp hist_origin [t_1;...;t_k]
        H && p_l(x) && H' -> C  
    with 
      - |H| = [n]
      - x = f(t_1,...,f(t_2,f(t_k,z))...)
      - apply_hist is the history of p_e(x) && p_l(y) -> p_l(f(x,y))

    The function returns the history of the following rule 
      H && p_e(t_1) && ... && p_e(t_k)  && H' -> C 
  *)
  let generate_tuple_hist apply_hist idx_hyp hist_origin elt_list = 
    let rec build n hist = function
      | [] -> Any(n,hist)
      | t::q ->
          let hist' = Resolution(apply_hist,n,hist) in
          build (n+1) hist' q
    in
    build idx_hyp hist_origin elt_list

  let find_all_elem_pred p_mem v cl =
    if exists_constraints (occurs_var v) cl.constraints || occurs_var_fact v cl.conclusion
    then None
    else
      try
        Some (List.filter_map (fun hyp -> match H.get_fact hyp with
          | Pred(p,[Var v']) when p.p_prop land Param.pred_TUPLE != 0 && v == v' -> None
          | Pred(p,[t;Var v']) when p == p_mem && v == v' -> 
              if occurs_var v t then raise Not_found;
              Some t
          | Pred(_,args) ->
              if List.exists (occurs_var v) args then raise Not_found;
              None
        ) cl.hypotheses)
      with Not_found -> None

  let transform_elim_rule p_mem v elt_list nb_elt cl =
    let (init_hist,rec_hist,f_cons) = List.assq p_mem !memberOptim_set in

    let rec build idx_hyp cur_t hist = function
      | [] -> hist, []
      | hyp::q_hyp -> 
          match H.get_fact hyp with
            | Pred(p_l,[Var v']) when v == v' ->
                let p_e = History.change_type_attacker p_l (List.hd p_mem.p_type) in
                let apply_hist = History.get_rule_hist (RApplyFunc(f_cons,p_l)) in
                
                let hist' = generate_tuple_hist apply_hist idx_hyp hist elt_list in
                let idx_hyp' = idx_hyp + nb_elt in

                let hist'',q_hyp' = build idx_hyp' cur_t hist' q_hyp in
                hist'', (H.create_list_strictly_before (List.map (fun t -> Pred(p_e,[t])) elt_list) hyp) @ q_hyp'

            | Pred(_,[t;Var v']) when v == v' ->
                (* We are in the case of the membership predicate *)
                let hist' = generate_elem_hist init_hist rec_hist idx_hyp hist cur_t in
                build idx_hyp (cur_t+1) hist' q_hyp
            | _ ->
                let hist', hypl' = build (idx_hyp+1) cur_t hist q_hyp in
                hist', hyp::hypl'
    in

    let hist, hypl = build 0 1 cl.history cl.hypotheses in
    { cl with history = hist; hypotheses = hypl }

  let elem_simplif next_stage repeat_next_stage cl =

    let rec find_optim seen_vars = function
      | [] -> next_stage cl
      | hyp::q_hyp ->
          match H.get_fact hyp with
            | Pred(p_mem,[t;Var v]) when p_mem.p_prop land Param.pred_ELEM != 0 && not (List.memq v seen_vars) ->
                begin match find_all_elem_pred p_mem v cl with
                  | None -> find_optim (v::seen_vars) q_hyp
                  | Some elt_list ->
                      repeat_next_stage (transform_elim_rule p_mem v elt_list (List.length elt_list) cl)
                end
            | _ -> find_optim seen_vars q_hyp
    in
    find_optim [] cl.hypotheses

  (* 11 - Eliminate redundant hypotheses 
    When R = H /\ H' -> C, and there exists \sigma such that
    \sigma H \subseteq H' and \sigma does not modify variables
    of H' and C, then R can be replaced with R' = H' -> C.
    This is a generalization of elimination of duplicate hypotheses.
    The function below does not really remove redundant hypotheses,
    but transforms them into duplicate hypotheses, so that
    they will be removed by the elimination of duplicate hypotheses.
    (In particular, in the history, they are coded as duplicate hypotheses.)

    Redundant hypotheses appear in particular when there are
    begin facts. They can slow down the subsumption test
    considerably.

    Note: it is important that elim_redundant_hyp comes as last
    simplification. In particular, it should come after elimination
    of attacker(x) (so that we don't have many hypotheses attacker(x)
    remaining, which can be mapped to any hypothesis attacker(..) in
    the instantiated clause) and after simplification of inequalities
    (so that we don't have inequalities with variables not
    used elsewhere, which cause problems for the subsumption test).
  *)

  (* Reordering hypotheses by size and bound variables *)

  let rec has_unbound_var = function
    Var v ->
      begin
        match v.link with
          NoLink -> true
        | TLink _
        | VLink _ -> false
        | _ -> Parsing_helper.internal_error __POS__ "unexpected link in has_unbound_var"
      end
  | FunApp(_,l) -> List.exists has_unbound_var l

  let fact_has_unbound_var = function
    Pred(_, tl) -> List.exists has_unbound_var tl

  let rank f =
    if fact_has_unbound_var f then
      fact_size f
    else
      1000000 (* Something probably bigger than all sizes of terms *)
  
  let rank_compare (_,r1) (_,r2) = r2 - r1

  let reorder_and_split hypl =
    let bound_hyp = ref [] in
    let unbound_hyp = ref [] in
  
    List.iter (fun hyp->
      let fact = H.get_fact hyp in
      if fact_has_unbound_var fact
      then unbound_hyp := (hyp,fact_size fact) :: !unbound_hyp
      else bound_hyp := hyp :: !bound_hyp
    ) hypl;
  
    let hyp_sorted = List.sort rank_compare !unbound_hyp in
    List.map (fun (f,_) -> f) hyp_sorted, !bound_hyp

  (* Marking of variables *)

  let rec is_marked_term = function
    | Var { link = VLink _ ; _ } -> true
    | Var _ -> false
    | FunApp(_,args) -> List.for_all is_marked_term args

  let is_marked_fact = function
    | Pred(_,args) -> List.for_all is_marked_term args

  let rec mark_variables = function
    | Var v ->
        begin match v.link with
          | TLink _ -> raise NoMatch
          | VLink _ -> ()
          | NoLink -> link v (VLink v)
          | _ -> Parsing_helper.internal_error __POS__ "[Rules.mark_variables] Unexpected links"
        end
    | FunApp(f,args) -> List.iter mark_variables args

  let mark_variables_fact = function
    | Pred(_,args) -> List.iter mark_variables args

  (* Matching of hypotheses *)

  let rec match_redundant_terms apply_mark t1 t2 = match t1, t2 with
    | Var v, Var v' when v == v' -> if apply_mark then mark_variables t2
    | Var v, _ ->
        begin match v.link with
          | NoLink ->
              if v.unfailing
              then
                begin
                  link v (TLink t2);
                  if apply_mark then mark_variables t2
                end
              else
                begin match t2 with
                  | Var v' when v'.unfailing -> raise NoMatch
                  | FunApp(f_symb,_) when f_symb.f_cat = Failure -> raise NoMatch
                  | _ ->
                      link v (TLink t2);
                      if apply_mark then mark_variables t2
                end
          | TLink t' ->
              (* Variables of [t'] have already been marked. *)
              if not (equal_terms t' t2)
              then raise NoMatch
          | VLink _ ->
              (* Since the variable has been marked, it can't be used in the substitution.
                The only possible case is when t1 = t2 which is already covered. *)
              raise NoMatch
          | _ -> Parsing_helper.internal_error __POS__ "[Rules.mark_variables] Unexpected links"
        end
    | FunApp (f1,args1), FunApp (f2,args2) ->
        if f1 != f2 then raise NoMatch;
        List.iter2 (match_redundant_terms apply_mark) args1 args2
    | _,_ -> raise NoMatch
  
  let match_redundant_hyp apply_mark hyp1 hyp2 = match H.get_fact hyp1, H.get_fact hyp2 with
    | Pred(p1,args1), Pred(p2,args2) ->
        if p1 != p2 then raise NoMatch;
        List.iter2 (match_redundant_terms apply_mark) args1 args2;
        H.match_ordering_for_redundant_hyp hyp1 hyp2
      

  let rec match_redundant_hypotheses_with_kept_hyp restwork hyp1 = function
    | [] -> raise NoMatch
    | hyp2 :: q2 ->
        try
          Terms.auto_cleanup_save (fun () ->
            match_redundant_hyp false hyp1 hyp2;
            restwork ()
          )
        with NoMatch ->
          match_redundant_hypotheses_with_kept_hyp restwork hyp1 q2

  let rec match_redundant_hypotheses_with_hyp restwork hyp1 passed_hyp = function
    | [] -> raise NoMatch
    | hyp2 :: q2 ->
        try
          Terms.auto_cleanup_save (fun () ->
            match_redundant_hyp true hyp1 hyp2;
            (* At that point, we need to keep hyp2 *)
            restwork hyp2 (List.rev_append passed_hyp q2)
          )
        with NoMatch ->
          match_redundant_hypotheses_with_hyp restwork hyp1 (hyp2::passed_hyp) q2

  let rec match_redundant_hypotheses restwork kept_hyp = function
    | [] -> restwork ()
    | hyp :: q ->
        (* We first test if [hyp] only contains marked variables *)
        if is_marked_fact (H.get_fact hyp)
        then match_redundant_hypotheses restwork (hyp::kept_hyp) q
        else
          try
            (* We first try by matching [hyp] and [kept_hyp] *)
            match_redundant_hypotheses_with_kept_hyp (fun () ->
              match_redundant_hypotheses restwork kept_hyp q
            ) hyp kept_hyp
          with NoMatch ->
            (* Since we did not find a match with kept facts,
              we try with the rest of the facts. *)
            try
              match_redundant_hypotheses_with_hyp (fun hyp' passed_hyp ->
                match_redundant_hypotheses restwork (hyp'::kept_hyp) passed_hyp
              ) hyp [] q
            with NoMatch ->
              (* No match was found hence [hyp] must be kept and we mark it. *)
              mark_variables_fact (H.get_fact hyp);
              match_redundant_hypotheses restwork (hyp::kept_hyp) q

  let elim_redundant_hyp next_stage repeat_next_stage cl =
    if (not !Param.redundant_hyp_elim) ||
      ( !Param.redundant_hyp_elim_begin_only && 
        (List.for_all (fun hyp -> match H.get_fact hyp with 
          | Pred({p_info = TestUnifP _}, _) -> true
          | Pred(p,_) -> p.p_prop land Param.pred_BLOCKING == 0
          ) cl.hypotheses
        )
      )
    then next_stage cl
    else
      let res = 
        assert(!Terms.current_bound_vars = []);

        try 
          Terms.auto_cleanup (fun () ->
            (* We mark the variables of the conclusion *)
            mark_variables_fact cl.conclusion;

            (* We look for a matching *)
            let (unbound_hyp,bound_hyp) = reorder_and_split cl.hypotheses in

            (* The facts in [bound_hyp] do not have unbound variables, meaning that all
              variables have been marked when executing [mark_variables_fact concl].
              They are therefore necessarily kept in [match_redundant_hyp]. *)

            match_redundant_hypotheses (fun () ->
              (* We check whether some match was found *)
              let success = List.exists (fun v -> match v.link with TLink _ -> true | _ -> false) !Terms.current_bound_vars in

              if success
              then
                begin
                  (* All variables in conclusion and hypotheses are linked either by a TLink or a VLink *)
                  let all_vars = !Terms.current_bound_vars in

                  (* It remains to check the disequalities and inequalities *)

                  (* We first save the links and remove the VLink *)
                  let saved_links =
                    List.map (fun v ->
                      let v_link = v.link in
                      begin match v_link with
                        | VLink _ -> v.link <- NoLink
                        | _ -> ()
                      end;
                      (v,v_link)
                    ) all_vars
                  in

                  (* We first copy the constraints without renaming variables. *)
                  let constra_inst = copy_constra3 cl.constraints in

                  (* We now remove all the links *)
                  List.iter (fun v -> v.link <- NoLink) all_vars;

                  (* We compare *)
                  try
                    (* We check the implication of constraints. *)
                    if not (TermsEq.implies_constraints (Some (fun () -> all_vars)) cl.constraints constra_inst) then
		      raise NoMatch;

                    (* We found a proper matching so we restore the TLink, copy the rule and run next_stage *)
                    List.iter (function (v,TLink t) -> v.link <- TLink t | (v,_) -> v.link <- NoLink) saved_links;

                    let cl' = C.copy3 { cl with constraints = constra_inst } in

                    (* Restore the links - It is in fact unecessary as the links will be cleanup by the previous
                       call of auto_cleanup but we keep it to preserve the invariant on Terms.current_bound_vars *)
                    List.iter (fun (v,link) -> v.link <- link) saved_links;

                    Some cl'
                  with NoMatch ->
                    (* Restore the links and raise Nomatch *)
                    List.iter (fun (v,link) -> v.link <- link) saved_links;
                    raise NoMatch
                end
              else raise NoMatch
            ) bound_hyp unbound_hyp
          )
        with NoMatch -> None
      in
      match res with
        | None -> next_stage cl
        | Some cl' -> repeat_next_stage cl'

  (* 12 - Simplification using the equational theory *)

  let simp_eq_rule next_stage cl =
    if TermsEq.hasConvergentEquations ()
    then
      try
        let evaluate = function 
          | Pred(p,l) ->
              if (!Param.simpeq_all_predicates) || (p.p_prop land Param.pred_SIMPEQ != 0)
              then List.iter TermsEq.simp_eq l
        in
        
        Terms.auto_cleanup (fun () ->
          evaluate cl.conclusion;
          List.iter (fun hyp -> evaluate (H.get_fact hyp)) cl.hypotheses
        );
        next_stage cl
      with TermsEq.Reduces ->
        () (* Remove the clause when a term reduces. *)
    else
      next_stage cl
  
  (* 13 - Simplification of conclusion to remove clauses that conclude
   non-constant attacker facts that contain ground public terms (they
   can be inferred by applying each function symbol one after the
   other).  *)

  let simplify_conclusion next_f cl = match cl.conclusion with
    | Pred({ p_info = AttackerBin _ | AttackerGuess _;_}, [t1;t2]) ->
        begin match t1 with
          | FunApp(_,[]) -> next_f cl
          | _ ->
            if not (Terms.is_ground_public t1 && Terms.equal_terms t1 t2)
            then next_f cl
        end
    | Pred({p_info = Attacker _;_}, [t]) ->
        begin match t with
          | FunApp(_,[]) -> next_f cl (* Keep the clauses -> att(c) needed to build ground public terms
					 Other clauses H -> att(c) will be removed by subsumption. *)
          | _ ->  if not (Terms.is_ground_public t) then next_f cl
        end
    | _ -> next_f cl

  (* 14 - Removal of useless events for lemmas *)

  let is_fact_only_for_lemma hyp = match H.get_fact hyp with
    | Pred(p,(FunApp(ev,args)::_)) when (p == Param.event_pred_block || p == Param.event2_pred_block || p == Param.inj_event_pred_block) && List.memq ev !events_only_for_lemmas -> true
    | _ -> false

  let is_fact_only_for_lemma_bad = function
    | Pred(p,(FunApp(ev,args)::_)) when (p == Param.event_pred_block || p == Param.event2_pred_block || p == Param.inj_event_pred_block) && List.memq ev !events_only_for_lemmas_without_options -> true
    | _ -> false

  let rec mark_variables_follow = function
    | Var { link = TLink t; _ } -> mark_variables_follow t
    | Var ({ link = NoLink; _ } as v)-> Terms.link v (VLink v)
    | Var _ -> ()
    | FunApp(_,args) -> List.iter mark_variables_follow args

  let rec mark_variables_follow_fact = function
    | Pred(_,args) -> List.iter mark_variables_follow args

  (* [inter_variables vars t] adds to [vars] to the marked variables in [t] *)
  let rec inter_variables vars = function
    | Var { link = TLink t; _} -> inter_variables vars t
    | Var ({ link = VLink _; _ } as v)->
        if not (List.memq v !vars)
        then vars := v :: !vars
    | Var _ -> ()
    | FunApp(_,args) -> List.iter (inter_variables vars) args

  let inter_variables_fact vars = function
    | Pred(_,args) -> List.iter (inter_variables vars) args

  let rec remove_from_list x = function
    | [] -> []
    | x'::q when x' == x -> q
    | x'::q -> x' :: (remove_from_list x q)

  (* [vars_not_in vars t] removes from [vars] the marked variables in [t].
    Raises [NoMatch] in case no variable remains in [vars]. *)
  let rec vars_not_in vars = function
    | Var { link = TLink t; _} -> vars_not_in vars t
    | Var ({ link = NoLink; _ } as v)->
        Terms.link v (VLink v);
        vars := remove_from_list v !vars;
        if !vars = []
        then raise NoMatch
    | Var _ -> ()
    | FunApp(_,args) -> List.iter (vars_not_in vars) args

  let vars_not_in_fact vars = function
    | Pred(_,args) -> List.iter (vars_not_in vars) args

  let vars_not_in_nat vars constra =
    List.iter (vars_not_in vars) constra.is_nat;
    List.iter (fun (x,_,y) ->
      vars_not_in vars x;
      vars_not_in vars y;
    ) constra.geq

  (* [is_forced_removal_rule_bad rule] is true when the clause [rule]
    is of the form H -> bad where H contains only unselectable facts
    and attacker2(x,y) for variables x,y.
    In this case, attacker2(x,y) will be selected, very likely yielding
    non-termination. In this case, we remove events useful only for lemmas
    (without option KeepEvents), by the function
    [remove_useless_events_for_lemma_bad]; that allows the removal of
    attacker2(...) facts containing variables common with events. We can
    then often obtain a simplified clause -> bad, and avoid the
    non-termination. *)

  let is_forced_removal_rule_bad cl = match cl.conclusion with
    | Pred(p,[]) when p == Param.bad_pred ->
        List.for_all (fun hyp -> match H.get_fact hyp with
          | Pred({p_info = AttackerBin _ | AttackerGuess _; _},args) -> List.for_all (function Var _ -> true | _ -> false) args
          | fact -> Terms.is_unselectable fact
        ) cl.hypotheses
    | _ -> false

  let remove_useless_events_for_lemma_bad cl =
    let rec remove_facts n hist = function
      | [] -> ([],hist)
      | fact :: q_fact ->
          let (q_fact',hist') = remove_facts (n+1) hist q_fact in

          if is_fact_only_for_lemma_bad (H.get_fact fact)
          then (q_fact',HRemovedBySimplification(n,hist'))
          else (fact::q_fact',hist')
    in

    let (hypl',hist') = remove_facts 0 cl.history cl.hypotheses in
    if cl.history == hist'
    then cl (* No modification *)
    else
      simplify_constraints_simple
        (elim_any_x { cl with history = hist'; hypotheses = hypl' })

  let remove_useless_events_for_lemma_main in_saturation lemmas cl =
    let check_one_fact_vs_one_fact_lemma fact sel_fact_end_or_inj_event_list begin_ev_fact_list fact_lem fact_lem_list =
      (* We have a clause [fact && sel_fact_end_or_inj_event_list && begin_ev_fact_list && constra => concl]
        and a lemma [fact_lem && fact_lem_list => ... ]
        We try to apply the lemma to a clause obtained by resolution from the clause
        above by unifying [fact] and [fact_lem]. Let [\sigma] be their mgu.
        If [possible_vars] is non-empty at the end of this function, the lemma can
        never be applied in this way on a clause obtained by resolution for the current
        clause, so we remove the event [fact] (since it is also useful only for lemmas).
        However, this transformation is complete in full generality, because the
        current clause can also be transformed by applied other lemmas at some point,
        which may later make an applicationn of a lemma using [fact] possible.

        Proof sketch: Let x be a variable in [possible_vars].
        x occurs in [fact_lem\sigma = fact\sigma]. So there is a variable y
        such that y occurs in [fact] and x occurs in y\sigma.
        x does not occur in [sel_fact_end_or_inj_event_list\sigma], [concl\sigma] and [nat_constra\sigma],
        so y does not occur in [sel_fact_end_or_inj_event_list], [concl], and [nat_constra].
        Hence during resolution from the clause [fact && sel_fact_end_or_inj_event_list && begin_ev_fact_list && constra => concl],
        the variable y will never be instantiated, so the clause obtained by resolution
        is [fact' && H && begin_ev_fact_list' => C] where y occurs in [fact'] (which is an instance of [fact]),
        y does not occur in H,C, and [begin_ev_fact_list'] is an instance of [begin_ev_fact_list].
        When we apply the lemma on this clause, [fact'] must be an instance of [fact_lem],
        so in fact y is left unchanged, i.e. y = x.
        The variable x does not occur in the events of [begin_ev_fact_list\sigma && H, C] that may
        be used to match [fact_lem_list\sigma], so y does not occur in the events of
        [begin_ev_fact_list' && H,C] that may be used to match [fact_lem_list].
        However, y = x occurs in [fact_lem_list\sigma]. The matching is then impossible.
        *)
      Terms.auto_cleanup (fun () ->
        try
          Terms.unify_facts (Terms.unblock_predicate_fact fact) fact_lem;

          let possible_vars = ref [] in
          Terms.auto_cleanup (fun () ->
            (* We start by marking the variables of fact_lem\sigma*)
            mark_variables_follow_fact fact_lem;

            (* We retrieve the variables that are also in fact_lem_list\sigma *)
            List.iter (inter_variables_fact possible_vars) fact_lem_list
          );
          if !possible_vars = []
          then false
          else
            begin
              try
                (* We remove from possible_vars the variables that are in the conclusion
                  and the potentially selectable facts, as well as injective events
                  and end events. *)
                Terms.auto_cleanup (fun () ->
                  List.iter (vars_not_in_fact possible_vars) (cl.conclusion::sel_fact_end_or_inj_event_list);
                  vars_not_in_nat possible_vars cl.constraints;
                );
                (* We remove from possible_vars the variables that are in the begin events
                  that can unify with the other premises of the lemma. Note that the application
                  of the lemma may also use the conclusion as well as end events and injective
                  events in the hypothesis. The variables of those have already been removed above. *)
                List.iter (fun fact_ev ->
                  if List.exists (fun fact_lem' -> are_unifiable_facts (Terms.unblock_predicate_fact fact_ev) fact_lem') fact_lem_list
                  then
                    Terms.auto_cleanup (fun () ->
                      vars_not_in_fact possible_vars fact_ev
                    )
                ) begin_ev_fact_list;
                true
              with NoMatch -> false
            end
        with Unify -> true
      )
    in
      
    let event_may_be_used = (S.selection_fun_nostatechange cl = -1) in

    (* [fact] is blocking and non_injective *)
    let check_one_fact_vs_lemma hyp hyp_list lemma =

      match lemma.l_premise with
        | [fact_lem] ->
            (* When there is only one fact in the premise of the lemma, we check that the lemma was already applied. The test is sound but not complete. *)
            if event_may_be_used && ((in_saturation && lemma.l_sat_app) || (not in_saturation && lemma.l_verif_app))
            then
              Terms.auto_cleanup (fun () ->
                try
                  match_facts_phase_geq fact_lem (Terms.unblock_predicate_fact (H.get_fact hyp));
                  true
                with NoMatch -> false
              )
            else false
        | _ ->
            (* When there is more than one fact in the premise of the lemma, we check that the lemma cannot be applied. The test is also not complete. *)
            let (sel_fact_end_or_inj_events,begin_ev_facts) =
              let hyp_list' = List.map H.get_fact hyp_list in
              List.partition (function  
                | Pred(p,_) when p == Param.event_pred_block || p == Param.event2_pred_block -> false
                | _ -> true
              ) hyp_list' in
            let rec go_through_premise fact_lem_list = function
              | [] -> true
              | fact_lem :: q_lem ->
                  if check_one_fact_vs_one_fact_lemma (H.get_fact hyp) sel_fact_end_or_inj_events begin_ev_facts fact_lem (List.rev_append fact_lem_list q_lem)
                  then go_through_premise (fact_lem::fact_lem_list) q_lem
                  else false
            in
            go_through_premise [] lemma.l_premise
    in

    let rec check_facts_in_hypl n rest_hypl hypl hist = match hypl with
      | [] -> ([],hist)
      | hyp :: q_hyp ->
          let (q_hyp',hist') = check_facts_in_hypl (n+1) (hyp::rest_hypl) q_hyp hist in

          if is_fact_only_for_lemma hyp
          then
            (* In that case, the event cannot be injective, because
              lemmas/axioms/restrictions cannot contain injective events and
              the considered event occurs only in lemmas/axioms/restrictions.
              So, if [fact] is an event we look for, it is necessarily
              non-injective and blocking (as it is in hypothesis of the clause)*)
            let hypl' = rest_hypl@q_hyp' in
            if List.for_all (check_one_fact_vs_lemma hyp hypl') lemmas
            then
              (* The fact has been found useless. We use HRemovedBySimplification for history but we should
                probably use a new one for clarity. *)
              (q_hyp',HRemovedBySimplification(n,hist'))
            else (hyp::q_hyp',hist')
          else (hyp::q_hyp',hist')
    in

    let (hypl',hist') = check_facts_in_hypl 0 [] cl.hypotheses cl.history in
    if cl.history == hist'
    then cl (* No modification *)
    else
      simplify_constraints_simple
      (elim_any_x { cl with history = hist'; hypotheses = hypl' })

  let remove_useless_events_for_lemma in_saturation lemmas cl =
    if lemmas <> [] && (not !sound_mode)
    then
      if is_forced_removal_rule_bad cl
      then remove_useless_events_for_lemma_bad cl
      else
        if !events_only_for_lemmas <> []
        then remove_useless_events_for_lemma_main in_saturation lemmas cl
        else cl
    else cl

  (* 15. Simplification on natural numbers. *)

  let rec may_be_nat_number = function
    | Var v -> true
    | FunApp(f,[t]) when f == Terms.succ_fun -> may_be_nat_number t
    | _ -> false

  (* Calls to [simplify_natural_number] are prevented on standard clauses in
    [normal_rule], in particular on the clauses for 0 and +1. *)
  let simplify_natural_number next_stage cl = match cl.conclusion with
    | Pred({p_info = Attacker _},[t]) when may_be_nat_number t ->
        begin
          let constra' = Terms.constraints_of_is_nat t in
          let get_vars_op = Some (fun () -> Terms.get_vars_fact cl.conclusion) in
          if not (TermsEq.implies_constraints get_vars_op cl.constraints constra')
          then next_stage cl
        end
    | Pred({p_info = AttackerBin _ | AttackerGuess _},[t1;t2]) when may_be_nat_number t1 && Terms.equal_terms t1 t2 ->
        begin
          let constra' = Terms.constraints_of_is_nat t1 in
          let get_vars_op = Some (fun () -> Terms.get_vars_fact cl.conclusion) in
          if not (TermsEq.implies_constraints get_vars_op cl.constraints constra')
          then next_stage cl
        end
    | _ -> next_stage cl

  (* 16. Application of lemmas *)
      
  (* [t] must contain only variables from the clause.
     It should have been copied (without renaming) before applying this function *)
  let rec match_one_subterm f_next pos_l t_sub t = match t with
    | Var _ | FunApp({ f_cat = Name _; _},_) ->
        Terms.auto_cleanup (fun () ->
          Terms.match_terms t_sub t;
          f_next (List.rev pos_l)
        )
    | FunApp(_,args) ->
        try
          Terms.auto_cleanup (fun () ->
            Terms.match_terms t_sub t;
            f_next (List.rev pos_l)
          )
        with NoMatch -> match_one_subterm_list f_next pos_l 1 t_sub args

  and match_one_subterm_list f_next pos_l i t_sub = function
  | [] -> raise NoMatch
  | t::q ->
      try
        match_one_subterm f_next (i::pos_l) t_sub t
      with NoMatch -> match_one_subterm_list f_next pos_l (i+1) t_sub q

  let match_subterms f_next l_subterm = 
    let subterms_inst = List.map (fun (t_sub,t) -> (t_sub,t,Terms.copy_term3 t)) l_subterm in

    let rec explore matched_sub = function
      | [] -> f_next matched_sub
      | (t_sub,t,t_inst)::q ->
          match_one_subterm (fun pos_l ->
            explore (pos_l::matched_sub) q
          ) [] t_sub t_inst
    in

    explore [] subterms_inst

  let rec match_one_premise f_next (match_fun:fact -> fact -> unit) (matched_prem:(int * hyp) list) (fact_lem:fact) (q_lem:fact list) (prev_hyp:(int * hyp) list) = function 
    | [] -> raise NoMatch
    | (i_hyp,hyp)::q_hyp ->
        try
          Terms.auto_cleanup (fun () ->
            (* Predicates in lemmas are all unblocking so we can always used match_facts_unblock.
               When the lemma is not inductive we can use greater phases, otherwise we use the same phase.
	       This is done via the function [match_fun]. *)
            
            match_fun fact_lem (H.get_fact hyp);
            match_all_premise f_next match_fun ((i_hyp,hyp)::matched_prem) (prev_hyp @ q_hyp) q_lem
          )
        with NoMatch ->
          match_one_premise f_next match_fun matched_prem fact_lem q_lem ((i_hyp,hyp)::prev_hyp) q_hyp

  and match_all_premise f_next match_fun matched_prem hyp_l = function
    | [] ->
        (* All premises have been checked *)
        f_next matched_prem
    | fact_lem::q_lem -> match_one_premise f_next match_fun matched_prem fact_lem q_lem [] hyp_l

  (*
    Invariant to respect on the event:
      If an event in the premise of the lemma is "inj" (requires occurence) and
      this event is required in conclusion for the main query, then this event for the
      conclusion should also be "inj". 
  *)
  let matching_lemma_premise f_next f_next_no_match lemma hypl_to_match cl =
    
    let match_fun = 
      if lemma.l_induction = None
      then Terms.match_facts_unblock_inj_phase_geq
      else Terms.match_facts_unblock_inj
    in

    try
      match_all_premise (fun matched_prem ->
        (* We check the constraints *)
        if not (TermsEq.implies_constraints3 None cl.constraints lemma.l_constra)
        then raise NoMatch;
      
        (* Check subterms *)
        match_subterms (fun matched_sub ->
          if
	    (* The plan will be to prove lemmas on bitraces only for traces that do not diverge.
	       When we apply a lemma on a proof of an equivalence, we can do it only
	       when we are sure that the trace does not diverge [C.is_lemma_applicable_for_equivalence].
	       When we apply a lemma on a proof of a correspondence, we know that we are on
	       a trace that does not diverge, so we can apply the standard condition. *)
            (not !is_equivalence_query && (lemma.l_induction = None || C.is_inductive_lemma_applicable lemma cl matched_prem)) ||
            (!is_equivalence_query && C.is_lemma_applicable_for_equivalence cl matched_prem)
          then f_next matched_prem matched_sub
          else raise NoMatch
        ) lemma.l_subterms
      ) match_fun [] hypl_to_match lemma.l_premise
    with NoMatch -> f_next_no_match ()

  let rec copy_term_and_record vars_ref = function
    | FunApp(f,l) as t ->
        let l' =  List.mapq (copy_term_and_record vars_ref) l in
        if l == l' then t else FunApp(f, l')
    | Var v -> match v.link with
        | NoLink -> 
            (* Existential variable *)
            let v' = copy_var v in
            let vt' = Var v' in
            Terms.link v (TLink vt');
            vars_ref := v' :: !vars_ref;
            vt'
        | TLink l -> l
        | _ -> Parsing_helper.internal_error __POS__ "[Rules.copy_term_and_record] unexpected link."

  let copy_fact_and_record vars_ref = function
    | Pred(p,l) as fact ->
        let l' = List.mapq (copy_term_and_record vars_ref) l in
        if l == l' then fact else Pred(p, l')

  (* In this function, we instantiate in priority existential variables from the lemma. *)
  let rec unify_for_lemma priority_vars t1 t2 = match (t1,t2) with
    | (Var v, Var v') when v == v' -> ()
    | (Var v, _) ->
        begin
          match v.link with
          | NoLink ->
              begin
                match t2 with
                | Var {link = TLink t2'} -> unify_for_lemma priority_vars t1 t2'
                | Var v' when v.unfailing ->
                          if List.memq v' priority_vars && v'.unfailing
                    then link v' (TLink t1)
                    else link v (TLink t2)
                | Var v' when v'.unfailing ->
                        link v' (TLink t1)
                | FunApp (f_symb,_) when f_symb.f_cat = Failure && v.unfailing = false -> raise Unify
                | Var v' when v'.vname.name = Param.def_var_name ->
                    if List.memq v priority_vars && not (List.memq v' priority_vars)
                    then link v (TLink t2)
                    else link v' (TLink t1)
                | Var v' ->
                    if List.memq v' priority_vars
                    then link v' (TLink t1)
                    else link v (TLink t2)
                | _ ->
                    occur_check v t2;
                          link v (TLink t2)
              end
          | TLink t1' -> unify_for_lemma priority_vars t1' t2
          | _ -> Parsing_helper.internal_error __POS__ "Unexpected link in unify 1"
        end
    | (FunApp(f_symb,_), Var v) ->
        begin
          match v.link with
            NoLink ->
              if v.unfailing = false && f_symb.f_cat = Failure
              then raise Unify
              else
                begin
                      occur_check v t1;
                  link v (TLink t1)
                end
          | TLink t2' -> unify_for_lemma priority_vars t1 t2'
          | _ -> Parsing_helper.internal_error __POS__ "Unexpected link in unify 2"
        end
    | (FunApp(f1, l1), FunApp(f2,l2)) ->
      if f1 != f2 then raise Unify;
      List.iter2 (unify_for_lemma priority_vars) l1 l2

  (* [match_for_lemma_all_hyp] is used to test if the facts that the
     lemma would add are already present in the clause *)
  let rec match_for_lemma exists_vars t1 t2 = match t1, t2 with
    | Var v, Var v' when v == v' -> ()
    | Var v, _ when not (List.memq v exists_vars) -> raise NoMatch
    | Var { link = TLink t;_}, _ -> if not (Terms.equal_terms t t2) then raise NoMatch
    | Var v, _ -> link v (TLink t2)
    | FunApp(f1,args1), FunApp(f2,args2) -> 
        if f1 != f2 then raise NoMatch;
        List.iter2 (match_for_lemma exists_vars) args1 args2 
    | _ -> raise NoMatch

  let match_for_lemma_hyp exists_vars hyp1 hyp2 = match H.get_fact hyp1, H.get_fact hyp2 with
    | Pred(p1,args1), Pred(p2,args2) ->
        if p1 != p2 then raise NoMatch;
        if not (Ordering.includes_clause (H.get_ordering_relation hyp1) (H.get_ordering_relation hyp2)) then raise NoMatch;
        List.iter2 (match_for_lemma exists_vars) args1 args2 

  let rec match_for_lemma_one_hyp f_next exists_vars hyp1 = function
    | [] -> raise NoMatch
    | hyp2::q2 ->
        let no_instantiated_vars = ref false in
        try 
          Terms.auto_cleanup (fun () ->
            match_for_lemma_hyp exists_vars hyp1 hyp2;
            if !current_bound_vars = [] then no_instantiated_vars := true;
            f_next ()
          )
        with NoMatch ->
          if !no_instantiated_vars
          then raise NoMatch
          else match_for_lemma_one_hyp f_next exists_vars hyp1 q2

  let rec match_for_lemma_all_hyp f_next exists_vars hyp_l1 hyp_l2 = match hyp_l1 with
    | [] -> f_next ()
    | hyp1::q1 ->
        match_for_lemma_one_hyp (fun () ->
          match_for_lemma_all_hyp f_next exists_vars q1 hyp_l2
        ) exists_vars hyp1 hyp_l2

  let apply_lemma cl lemma matched_prem matched_sub =
    (* At that point, we assume that the premise of the lemma has been matched. Hence all variables in 
       the conclusion of the lemma that do not have a link are necessarily existential. We refresh these
       variables. *)
       
    let exists_vars = ref [] in

    let conclusion_lemma =
      Terms.auto_cleanup (fun () ->
        List.mapi (fun i (fact_lem, constra_lem, eqs_lem) ->
          i,
          List.map (fun (fact,qrel) -> copy_fact_and_record exists_vars fact, qrel) fact_lem,
          Terms.map_constraints (copy_term_and_record exists_vars) constra_lem, 
          List.map (fun (t1,t2) -> copy_term_and_record exists_vars t1, copy_term_and_record exists_vars t2) eqs_lem 
        ) lemma.l_conclusion
      )
    in

    let instantiates_only_existential_vars vars =
      List.for_all (fun v -> List.memq v !exists_vars) vars
    in
    
    let prepare_generate_added_hyp = 
      lazy (
        let concl_pred_list = match cl.conclusion with
          | Pred({ p_info = Combined(_,_,pl); _},_) -> pl
          | Pred(p,_) -> [p]
        in
        H.create_from_lemma_application concl_pred_list matched_prem
      )
    in

    let generate_added_hyp fact_lem = 
      List.fold_right (fun (fact,qrel) (acc_hyp,acc_hist) ->
        match (Lazy.force prepare_generate_added_hyp) fact qrel with
          | None -> acc_hyp, (false::acc_hist)
          | Some hyp -> (hyp::acc_hyp), (true::acc_hist)
      ) fact_lem ([],[])
    in

    let hist_match_hyp = List.rev_map (fun (i,_) -> i) matched_prem in
    let hist_sub = List.rev matched_sub in

    let generated_clauses = ref [] in

    let generate_new_clause (only_inst_exist_vars:bool) i is_hyp_added hyp_to_add constra_lem =
      
      let new_cl1 = 
        { cl with
          hypotheses = cl.hypotheses @ hyp_to_add;
          constraints = Terms.wedge_constraints cl.constraints constra_lem;
          history = HLemma(lemma,hist_match_hyp,hist_sub,(i,is_hyp_added),cl.history)
        }
      in
      let new_cl2 = Terms.auto_cleanup (fun () -> C.copy2 new_cl1) in

      simplify_constraints (fun cl ->
        generated_clauses := (only_inst_exist_vars,cl) :: !generated_clauses
      ) (fun cl ->
        generated_clauses := (only_inst_exist_vars,cl) :: !generated_clauses
      ) new_cl2
    in

    List.iter (fun (i,fact_lem,constra_lem,eqs_lem) ->
      try 
        Terms.auto_cleanup (fun () ->
          (* Unify the equalities *)
          List.iter (fun (t1,t2) -> unify_for_lemma !exists_vars t1 t2) eqs_lem;

          if instantiates_only_existential_vars !current_bound_vars
          then
            (* We need to check that the added hyp already exists *)
            let hyp_to_add, is_hyp_added = generate_added_hyp fact_lem in
            let hyp_to_add' = List.map H.copy4 hyp_to_add in
            let get_vars () = Terms.get_vars_generic C.iter_term_exclude_constraint cl in
            if 
              try 
                match_for_lemma_all_hyp (fun () ->
                  if not (TermsEq.implies_constraints4 (Some get_vars) cl.constraints constra_lem)
                  then raise NoMatch;
                  true
                ) !exists_vars hyp_to_add' cl.hypotheses
              with NoMatch -> false
            then raise NoMatch
            else generate_new_clause true i is_hyp_added hyp_to_add' constra_lem
          else
            (* In that case, we can generate the new clause *)
            let hyp_to_add, is_hyp_added = generate_added_hyp fact_lem in
            generate_new_clause false i is_hyp_added hyp_to_add constra_lem
        )
      with Unify -> ()
    ) conclusion_lemma;

    (* The clauses are now accumulated in [generated_clauses] *)
    !generated_clauses

  exception LemmaApplied of (bool * clause) list

  let simplify_lemmas next_stage_no_match next_stage do_not_apply lemma_list cl = 
    if lemma_list = [] || do_not_apply
    then next_stage_no_match cl
    else 
      (* [only_inst_exists_vars_opt = None] when we have applied no lemma;
        [only_inst_exists_vars_opt = Some only_inst_exists_vars] when we have applied a lemma
        and it has instantiated variables of the clause iff not [only_inst_exists_vars] *)
      let rec match_and_apply_lemmas only_inst_exists_vars_opt cl =
        let hypl_to_match = List.mapi (fun i hyp -> (i,hyp)) cl.hypotheses in
        let hypl_to_match_with_concl = 
          let fact_l_concl = Terms.fact_list_of_conclusion cl.conclusion in
          let hypl, _ =
	    (* Conclusion facts are represented by a negative index [n < 0] *)
            List.fold_left (fun (acc_hypl,n) fact -> 
              ((n,H.create_hypothesis_from_nth_conclusion (-n) fact)::acc_hypl), n-1
            ) (hypl_to_match,-1) fact_l_concl
          in
          hypl
        in
        match_and_apply_all only_inst_exists_vars_opt hypl_to_match hypl_to_match_with_concl cl lemma_list 

      and match_and_apply_all only_inst_exists_vars_opt hypl_to_match hypl_to_match_with_concl cl = function 
        | [] -> 
            begin match only_inst_exists_vars_opt with
              | Some only_inst_exists_vars -> next_stage only_inst_exists_vars cl
              | None -> next_stage_no_match cl
            end
        | lem::q ->
            let hypl = 
              if (lem.l_induction = None || C.allow_conclusion_for_induction cl) && not (Terms.is_bad cl.conclusion)
              then hypl_to_match_with_concl 
              else hypl_to_match
            in

            try 
              (* Matching the premise *)
              matching_lemma_premise (fun matched_prem matched_sub ->
                (* The lemma can be applied. We check wether it hasn't already been applied 
                  or does not produce new information *)
                let new_clauses = apply_lemma cl lem matched_prem matched_sub in
                (* We use an exception so that we can cleanup the links added when matching the lemma premises. *)
                raise (LemmaApplied new_clauses)
              ) (fun () ->
                match_and_apply_all only_inst_exists_vars_opt hypl_to_match hypl_to_match_with_concl cl q
              ) lem hypl cl
            with LemmaApplied cl_list ->
              List.iter (fun (only_inst_exists_vars,cl) -> 
                let only_inst_exists_vars_opt' = match only_inst_exists_vars_opt with
                  | None -> Some only_inst_exists_vars
                  | Some _ -> only_inst_exists_vars_opt
                      (* We cannot take into account that the new application of a lemma
                        may have instantiated variables of the initial clause, because
                        it may happen that the first application creates new variables, and
                        the next application of a lemma instantiates those variables thinking
                        they are variables of the initial clause (which they are not). *)
                in
                match_and_apply_lemmas only_inst_exists_vars_opt' cl
              ) cl_list
      in
      
      match_and_apply_lemmas None cl

  (* Remove events in clauses H -> bad that contain only events in hypothesis *)

  let remove_equiv_events next_stage cl =
    if !sound_mode then
      next_stage cl
    else
      W.remove_equiv_events next_stage cl
	
  (* Combining all simplification rules: normalisation function *)

  (* [is_standard_clause r] returns true when the clause [r] must be protected from simplifications *)
  let is_standard_clause cl =
    (match cl.history with
    | Rule(_,tag,_,_,_) ->
        begin
          match tag with
          | PhaseChange (* phase clause *)
          | Rl _ (* listening clause *)
    | LblEquiv -> true
          | Apply(f, _) (* data constructor or projection clause *) ->
        Terms.is_data_or_proj f
          (* Clauses for data constructors
        att(x1) && ... && att(xn) -> att(f(x1...xn))
        att'(x1,y1) && ... && att'(xn,yn) -> att'(f(x1...xn),f(y1...yn))
      and projections
                    att(f(x1...xn)) -> att(xi)
        att'(f(x1...xn),f(y1...yn)) -> att'(xi,yi)
      as well as clauses LblEquiv must be preserved for the decomposition
      of data constructors and the replacement of equivalent facts
      performed in [decompose_hyp_tuples] and [decompose_concl_tuples]
      to be sound.
      In particular, clauses for the data constructors 0 and +1
      must be preserved for the simplification of natural numbers
      performed in [simplify_natural_number] to be sound. *)
          | _ -> false
        end
    | _ -> false) ||
      W.is_standard_clause cl || N.is_standard_clause cl

  let normal_rule database lemmas cl =

    let rec normal_rule do_not_apply_lemma cl =
      assert (!Terms.current_bound_vars == []);
      simplify_conclusion (fun cl ->
        decompose_hyp_tuples_rule (fun cl ->
          simp_eq_rule (fun cl ->
            elim_not (fun cl ->
              W.simplify (fun cl ->
                N.simplify (fun cl ->
                  decompose_concl_tuples (fun cl ->
                    elim_taut (fun cl ->
                      elim_any_x_rule (fun cl ->
                        simplify_constraints (fun cl ->
                          simplify_natural_number (fun cl ->
                            elem_simplif (fun cl ->
                              elim_redundant_hyp (fun cl ->
                                simplify_lemmas (fun cl ->
                                  remove_equiv_events normal_rule_add_rule cl
                                ) normal_rule do_not_apply_lemma lemmas cl
                              ) (normal_rule do_not_apply_lemma) cl
                            ) (normal_rule do_not_apply_lemma) cl
                          ) cl
                        ) (normal_rule do_not_apply_lemma) cl
                      ) cl
                    ) cl
                  ) cl
                ) (normal_rule do_not_apply_lemma) cl
              ) (normal_rule do_not_apply_lemma) cl
            ) cl
          ) cl
        ) cl
      ) cl

    (* Note that currently, we apply remove_useless_events_for_lemma on all clauses but we could as an
     alternative only apply it on clauses with the conclusion selected. *)
    and normal_rule_add_rule cl = 
      let cl' = (remove_useless_events_for_lemma true lemmas (limit_depth (limit_length cl))) in
      DB.add_rule database cl'
    in

    if is_standard_clause cl 
    then 
      (* [simplify_conclusion] must be applied to the projection clauses
        att'(f(x1...xn),x) && x <> f(g1...gn) -> att'(xi, fail)
        (see weaksecr.ml)
        It does not affect other standard clauses, so it is fine to
        apply it to all standard clauses *)
      simplify_conclusion (DB.add_rule database) cl
    else normal_rule false cl

  (* During solving, the standard clauses have already been included in the
     database, so we do not need to protect them any more. *)
  let normal_rule_solving database lemmas cl =

    let rec normal_rule do_not_apply_lemma cl =
      assert (!Terms.current_bound_vars == []);
      decompose_hyp_tuples_rule (
        elim_not (
          W.simplify (
            elim_any_x_rule (
              simplify_constraints (
                elem_simplif (
                  elim_redundant_hyp (
                    simplify_lemmas normal_rule_add_rule normal_rule do_not_apply_lemma lemmas
                  ) (normal_rule do_not_apply_lemma)
                ) (normal_rule do_not_apply_lemma)
              ) (normal_rule do_not_apply_lemma)
            )
          ) (normal_rule do_not_apply_lemma)
        )
      ) cl

    and normal_rule_add_rule cl = DB.add_rule database (remove_useless_events_for_lemma false lemmas cl) in

    normal_rule false cl

  (* Composition, that is, resolution
     [compose_clause] unifies the conclusion of [cl_solved] with the selected hypothesis [hyp]
     of [cl_unsolved].
     There must be no selected hypothesis in [cl_solved], and a selected hypothesis in [cl_unsolved]

     cl_solved = F1 & ... & Fn -> F0
     cl_unsolved = F'1 & ... & F'n' -> F'0
     can be resolved into
      s F1 & ... & s Fn & s F'2 & ... & s F'n -> s F'0
     where s is the most general unifier of F0 and F'1
     if F'1 selected
     and for all Fi, Fi not selected *)

  let rec replace_and_copy2_aux l1 hyp l = match l1 with
    | [] -> List.map H.copy2 l
    | t::q -> (H.copy2 (H.create_from_composition t hyp))::(replace_and_copy2_aux q hyp l)

  let rec replace_and_copy2 l1 n hyp = function
      [] -> Parsing_helper.internal_error __POS__ "replace_and_copy2"
    | (a::l) ->
        if n = 0
        then replace_and_copy2_aux l1 hyp l
        else (H.copy2 a)::(replace_and_copy2 l1 (n-1) hyp l)

  let compose_clause next_stage cl_solved cl_unsolved (sel_index,hyp) = 
    assert (!current_bound_vars == []);
    try
      let cl_unsolved' = 
        Terms.auto_cleanup (fun () ->
          Terms.unify_facts cl_solved.conclusion (H.get_fact hyp);
          {
            hypotheses = replace_and_copy2 cl_solved.hypotheses sel_index hyp cl_unsolved.hypotheses;
            conclusion = copy_fact2 cl_unsolved.conclusion;
            history = Resolution(cl_solved.history, sel_index, cl_unsolved.history);
            constraints = wedge_constraints (copy_constra2 cl_solved.constraints) (copy_constra2 cl_unsolved.constraints)
          }
        )
      in
      next_stage cl_unsolved'
    with Unify -> ()

  (* Redundancy *)

  (* Redundancy test [redundant ruleset annotinitrule]
    [ruleset] must be a set of clauses with empty selection
    [annotinitrule] must be a clause with empty selection
    The test returns true if and only if the clause [annotinitrule] can be derived
    with a derivation containing clauses in [ruleset].
  *)

  (* We show some invariant for the testing of global redundancy:

    During both the saturation procedure, we will compose the ongoing rule with a rule
    that has unselectable hypotheses. Hence, these rules are of the form:
      R = constraints && B && Ax -> C
    where B is a conjunction of blocking predicate, Ax is a conjunction of att(x) and/or comp(x).
    When C is the fact att(x) or comp(x), Ax does not contain att(x) or comp(x) for the same x.
    (Ax cannot contain C, because R would be a tautology,
    so it would be removed. The only other possibilities are that:
    - R = ... & att(x) -> comp(x): impossible because there are no clauses with comp as conclusion
    and another predicate as hypothesis
    - R = ... & comp(x) -> att(x): impossible because all clauses that have comp as hypothesis
    and att as conclusion have a name function symbol as root of the conclusion.)

    We will denote R -> R' a rule R' obtained by composing R with a rule with unselectable hypotheses.

    We can show that all Rinit ->^* R, the rule R is of the form:
      constraints && B && Ax && Am && Anu -> C
    where B is a conjunction of blocking predicates, Ax is a conjunction of att(x) or comp(x),
    Am and Anu are conjunctions of att(M) and/or comp(M) where vars(M) \subseteq vars(C) and
    x is not just a variables,
    facts in Anu match a nounif declaration with weight < dummy_weight = -4000, facts in Am do not.

    Notice that during saturation, the first rule is C -> C.
    Take Rc an unselectable rule constraints' && B' && Ax' -> C' such that \sigma = mgu(C,C'). For the redundancy
    to work, we need C to be unchanged by \sigma, i.e. C\sigma = C.
    This implies that the resulting clause is of the form:
      constraints'\sigma && B'\sigma && Ax'\sigma -> C
    We can split Ax'\sigma as Ax && Am && Anu where facts of Ax are att(x) or comp(x),
    facts of Anu are other facts that match a nounif declaration with weight < dummy_weight.

    Given a rule R, we'll use the notation B(R), Ax(R), Am(R) and Anu(R) for the corresponding
    conjunctions of facts. Finally, we write F1 && ... && Fn < F1' && ... && Fm' when
    {{ |F1|, ..., |Fn| }} <_m {{ |F1'|, ..., |Fm'| }} with <_m is the order on multiset.

    We can show that for all R -> R',
      - B(R)\sigma'' \subseteq B(R') (possibly instantiated due to simplification of constraints)
      - Anu(R) \subseteq Anu(R')
      - Am(R') < Am(R)

    Take a rule R = constraints && B && Ax && Am && Anu -> C with a selectable hypothesis F. This hypothesis
    must be in Am since B are blocking, Ax are att(x) or comp(x), and Anu are matching a nounif
    declaration with weight < dummy_weight.
    Hence Am = Am' && F.

    Take Rc an unselectable rule constraints' && B' && Ax' -> C' such that \sigma = mgu(F,C'). For the redundancy
    to work, we need C to be unchanged by \sigma, i.e. C\sigma = C. But vars(F) \subseteq vars(C)
    hence F\sigma = F. This implies that the resulting clause is of the form:
      constraints && constraints'\sigma && B && Ax && Am' && Anu && B'\sigma && Ax'\sigma -> C
    We can split Ax'\sigma as Ax'' && Am'' && Anu'
    where facts of Ax'' are att(x) or comp(x), facts of Anu' are other facts that match a nounif declaration.
    Note that, when C' is not the fact att(x) or comp(x),
    the facts of Am'' are att(y)\sigma where y is a variable of C', so we have Am'' < C'\sigma = F.
    When C' is att(x) or comp(x), Ax' does not contain att(x) or comp(x) for the same x,
    hence Ax'\sigma = Ax', so Ax'' = Ax', and Am'' and Anu' are empty. Therefore, in both cases,
    Am' && Am'' < Am, which concludes the proof.

    Note that these invariants are preserved by application of elim_any_x (the facts att(x) or comp(x)
    in Ax have a variable that occurs in B, Am, Anu, C, since they were not removed before,
    hence in B or C since the variables of Am, Anu are in C, hence they remain after elim_any_x) and decompose_hyp_tuples.
    The simplification of constraints may instantiate variables of Ax with succ(...succ(x)) or
    succ(...succ(0)). The succ and 0 are removed by decompose_hyp_tuples. The remaining fact att(x) is in Ax.
    The variables of Am, Anu, C cannot be instantiated by the simplification of constraints
    because they all occur in C and C must remain unchanged.
    Can variables of B be instantiated?
      The only common variables between constraints and constraints'\sigma are variables of C,
      which cannot be instantiated. Moreover [constraints] is already simplified.
      Even with that, variables of B can be instantiated in very particular cases. For instance:
      y is a variable of C => cannot be instantiated
      x is a variable of B not in C.
      constraints = x<>y, x<>y+2 is_nat(x) [y may not be nat]  constraints'\sigma = is_nat(y)
      is_nat(x,y) implies that case distinctions are made. The case y<x, x<y+2 implies
      x = y+1 => x is instantiated into y+1.

    Since for all R ->^+ R', Am(R') < Am(R) and all variables of Am(R') and Am(R) are in their respective
    conclusion, we deduce that R cannot subsume R'. So we need not verify that the current rule is not
    subsumed by a previously seen clause in the same branch. Furthermore, we have a termination guarantee.

    Finally, if R ->^* R' and B(R') cannot subsume the hypothesis of [initrule], where the subsumption test
    is computed using set inclusion instead of multiset inclusion (we need set inclusion because
    variables of B may be instantiated, possibly making two elements of B equal; the duplicate element
    is then removed in decompose_hyp_tuples), then we know
    that for all R' ->^* R'', R'' cannot subsume [initrule], so we can stop searching from R'.
  *)

  module MakeRedundant (SetR:
    sig
      type elt
      type t
      val iter_unifiable : (elt -> unit) -> t -> fact -> unit
      val get_clause : elt -> clause
      val is_unselectable : elt -> bool
    end) =
  struct
    exception Redundant

    let counter_redundant = ref 0

    let redundant first_cl_set rest_cl_set ((target_cl,_) as annot_target_cl)=

      let rec check_fun cl = 
        if Terms.are_matched_facts cl.conclusion target_cl.conclusion then
          let r' = elim_any_x (DB.simplify_hypotheses (decompose_hyp_tuples cl)) in
          let annot_r' = Sub.generate_subsumption_data r' in
          let (r_implies,block_set_implies) = Sub.implies_redundant annot_r' annot_target_cl in
          if r_implies
          then raise Redundant
          else if block_set_implies
          then redundant_rec annot_r'

      and redundant_rec (cl,_) =
        let sel_index = S.selection_fun { cl with conclusion = Param.dummy_fact } in
        if sel_index != -1 then

          let sel_fact = List.nth cl.hypotheses sel_index in

          if not (Ordering.is_pred_to_prove_fact (H.get_fact sel_fact))
          then
            let apply elt =
              (* In the set of clause with conclusion selected, the additional data represents whether
                the clause contains only unselectable hypotheses. *)
              (* if elt.Set.additional_data *)
              if SetR.is_unselectable elt
              then
                (* let (elt_clause,_) = elt.annot_clause in *)
                let elt_clause = SetR.get_clause elt in
                compose_clause (simplify_constraints check_fun check_fun) elt_clause cl (sel_index,sel_fact)
            in
            
            SetR.iter_unifiable apply rest_cl_set (H.get_fact sel_fact)
      in

      let apply first_cl =
        try
          let first_rule' =
            auto_cleanup (fun () ->
              Terms.match_facts first_cl.conclusion target_cl.conclusion;
              C.copy2 first_cl
            )
          in
          check_fun first_rule';
          false
        with NoMatch -> false
      in

      try 
        Set.exists apply first_cl_set
      with Redundant ->
        if !Param.verbose_redundant then
          begin
            incr counter_redundant;
            Printf.printf "Redundant rule eliminated %d:\n" !counter_redundant;
            C.Text.display_indep target_cl
          end;
        true
  end

  module Redundant = MakeRedundant(
    struct
     type elt = bool Set.element 
     type t = bool Set.t 
     let iter_unifiable = Set.iter_unifiable
     let get_clause elt = 
        let (cl,_) = elt.Set.annot_clause in
        cl [@@inline]
      let is_unselectable elt = elt.Set.additional_data [@@inline]
    end)

  let redundant_glob database annot_target_cl =
    !Param.redundancy_test <> Param.NoRed && Redundant.redundant database.DB.base_ns database.DB.base_ns annot_target_cl

  (* Saturates the rule base, by repeatedly applying the composition [compos_clause] *)

  let complete_rules database lemmas =
    let normal_rule = normal_rule database lemmas in
    let rec search_fix_point () = match Q.get database.DB.queue with
      | None ->
          Display.stop_dynamic_display ();
          Set.to_list database.DB.base_ns
      | Some ((cl, _, sub_data) as annot_rule) ->
          let sel_index = S.selection_fun cl in

          if sel_index == -1
          then
            begin
              if not (redundant_glob database (cl, sub_data))
              then
                begin
                  let is_unselectable = List.for_all (fun hyp -> is_unselectable (H.get_fact hyp)) cl.hypotheses in
                  (* Consider only clauses with unselectable hypotheses in redundancy
                    to help termination of the search for a derivation.
                    (In general, the termination of resolution is not guaranteed.
                    With this condition, the facts usable by resolution
                    are smaller in the hypothesis than in the conclusion, which implies termination.) *)
                  Set.add database.DB.base_ns annot_rule None is_unselectable;
                  DB.display_dynamic_statistics database;
                  Set.iter_unifiable (fun elt ->
                    let (elt_clause,_) = elt.annot_clause in
                    let selected_hyp = match elt.selected_fact with
                      | Some hyp -> hyp
                      | None -> Parsing_helper.internal_error __POS__ "[Rules.complete_rules] The base_sel should have selected fact"
                    in
                    compose_clause normal_rule cl elt_clause (elt.additional_data,selected_hyp)
                  ) database.DB.base_sel cl.conclusion;
                end
            end
          else
            begin
              let sel_fact = List.nth cl.hypotheses sel_index in

              Set.add database.DB.base_sel annot_rule (Some sel_fact) sel_index;
              DB.display_dynamic_statistics database;
              Set.iter_unifiable (fun ns_elt ->
                let (ns_elt_clause,_) = ns_elt.annot_clause in
                compose_clause normal_rule ns_elt_clause cl (sel_index,sel_fact)
              ) database.DB.base_ns (H.get_fact sel_fact);
            end;

          DB.display_rule_during_completion database (cl,sel_index);
          search_fix_point ()
    in
    search_fix_point ()
end

module SimplificationRules = 
  MakeSimplificationRules
    (Hyp)(Std)(Selfun.Std)(Weaksecr.Std)(Noninterf.Std)(Database.SubClause)(Database.SetClause)(Database.QueueClause)(Database.DB)

module SimplificationRulesOrd = 
  MakeSimplificationRules
    (HypOrd)(Ord)(Selfun.Ord)(Weaksecr.Ord)(Noninterf.Ord)(Database.SubOrdClause)(Database.SetOrdClause)(Database.QueueOrdClause)(Database.DBOrd)    

(* Liveness transformation *)

let requires_liveness () =
  !events_for_second_saturation <> [] || !predicates_for_second_saturation <> []

let prepare_clause_for_liveness cl =

  let unblock_hyp = HypOrd.map_fact unblock_predicate_fact in

  let rec analyse hist added_hyp n = function
    | [] -> hist, List.rev added_hyp
    | hyp :: q_hyp ->
        match HypOrd.get_fact hyp with
          | Pred(p,FunApp(f_ev,args)::_) when 
            (p == Param.event_pred_block || 
            p == Param.inj_event_pred_block ||
            p == Param.event2_pred_block) &&
            List.memq f_ev !events_for_second_saturation ->
              let fstatus = Pievent.get_event_status !Param.current_state f_ev in
              let fresh_occ, ublock_hyp = match fstatus.end_status with
                | WithOcc -> 
                    (* Begin predicate could be with occurrence or without. *)
                    if p == Param.event_pred_block
                    then true, HypOrd.map_fact (fun _ -> Pred(Param.inj_event_pred,[FunApp(f_ev,args);Terms.new_var_def_term Param.occurrence_type])) hyp 
                    else false, unblock_hyp hyp
                | NoOcc ->
                    (* Begin predicate should also be NoOcc *)
                    false, unblock_hyp hyp
                | No -> Parsing_helper.internal_error __POS__ "An event considered for second saturation should have an end status." 
              in
              analyse (HLiveness(n,fresh_occ,hist)) (ublock_hyp :: added_hyp) (n+1) q_hyp
          | Pred({ p_info = Block p; _},_) when List.memq p !predicates_for_second_saturation ->
              analyse (HLiveness(n,false,hist)) (unblock_hyp hyp  :: added_hyp) (n+1) q_hyp
          | _ -> analyse hist added_hyp (n+1) q_hyp
  in

  let (hist,added_hypl) = analyse cl.Ord.history [] 0 cl.Ord.hypotheses in

  if hist == cl.Ord.history
  then None (* No change *)  
  else Some { cl with history = hist; hypotheses = cl.Ord.hypotheses@added_hypl }

(* Global redundancy solving *)

module RedundantSolved = SimplificationRulesOrd.MakeRedundant(
  struct
    type elt = Ord.clause
    type t = Database.SetSatClause.t
    let iter_unifiable = Database.SetSatClause.iter_unifiable
    let get_clause elt = elt [@@inline]
    let is_unselectable _ = true [@@inline]
  end)

let redundant_glob_solving database sat_clauses annot_target_cl = 
  !Param.redundancy_test <> Param.NoRed && 
  RedundantSolved.redundant database.Database.DBOrd.base_ns sat_clauses annot_target_cl

let redundant_final_solving database sat_clauses =
  if !Param.redundancy_test = Param.BestRed
  then
    begin
      Display.Text.print_string "Removing redudant clauses.\n";
      flush_all ();
      Database.SetOrdClause.iter (fun elt ->
        (* By deactivating the clause, the application of [redundant rulelist' elt.sub_data elt.clause] will behave
            as if the rule elt.clause was not in the list [rulelist']. *)
        Database.SetOrdClause.deactivate database.Database.DBOrd.base_ns elt;

        (* If the clause is redundant, we leave it deactivated which corresponds to removing it from the database.
            Hence, if the clause is not redundant, it is important to reactivate it! *)
        if not (RedundantSolved.redundant database.Database.DBOrd.base_ns sat_clauses elt.Database.SetOrdClause.annot_clause)
        then Database.SetOrdClause.activate database.Database.DBOrd.base_ns elt;
      ) database.Database.DBOrd.base_ns
    end 

(* Complete rules solving *)

let complete_rules_solving database sat_clauses sat_clauses_for_redundant_glob apply_final_redundant lemmas =
  Parsing_helper.debug (fun () ->
    Display.stop_dynamic_display ();
    Parsing_helper.debug_msg "--- Entering complete_rules_solving";
    Parsing_helper.debug_msg "Checking database...";
    Database.DBOrd.check_no_link database;
    Parsing_helper.debug_msg "Checking saturated clauses...";
    Database.SetSatClause.iter (fun cl ->
      Ord.iter_term Terms.check_no_link cl;
      (* History.iter_term_history Terms.check_no_link cl.history; *)
    ) sat_clauses;
    Parsing_helper.debug_msg "Checking successful";
  );

  let normal_rule = SimplificationRulesOrd.normal_rule_solving database lemmas in

  let rec search_fix_point () = match Database.QueueOrdClause.get database.Database.DBOrd.queue with
    | None ->
        Display.stop_dynamic_display ();
        if apply_final_redundant then redundant_final_solving database sat_clauses_for_redundant_glob;
        Database.SetOrdClause.to_list database.Database.DBOrd.base_ns
    | Some (cl, feature_vector, sub_data) ->    
        let (sel_index,cl') =
          let sel_index_intermediate = Selfun.Ord.selection_fun { cl with conclusion = Param.dummy_fact } in
          if sel_index_intermediate == -1
          then Selfun.Ord.selection_fun_ignore_nounif cl
          else sel_index_intermediate, cl
        in
        
        let annot_cl' = (cl',feature_vector,sub_data) in

        if sel_index == -1
        then
          begin
            if not (redundant_glob_solving database sat_clauses_for_redundant_glob (cl', sub_data))
            then
	      begin
                (* The additional data boolean has no value here, we use [true]. *)
		Database.SetOrdClause.add database.Database.DBOrd.base_ns annot_cl' None true;
		Database.DBOrd.display_dynamic_statistics database
	      end;
          end
        else
          begin
            let sel_fact = List.nth cl'.hypotheses sel_index in
            Database.SetOrdClause.add database.Database.DBOrd.base_sel annot_cl' (Some sel_fact) sel_index;
            Database.DBOrd.display_dynamic_statistics database;
            Database.SetSatClause.iter_unifiable (fun sat_rule -> 
              SimplificationRulesOrd.compose_clause normal_rule sat_rule cl' (sel_index,sel_fact)
            ) sat_clauses (HypOrd.get_fact sel_fact)
          end;

        Database.DBOrd.display_rule_during_completion database (cl',sel_index);
        search_fix_point ()
  
  in
  search_fix_point ()

(* Solving request rule *)

let saturated_rules = ref []
let set_saturated_rules = ref Database.SetSatClause.empty
let set_saturated_rules_for_redundant_glob = ref Database.SetSatClause.empty

let solving_request_rule ?(close_equation=true) lemmas cl =
  assert (!initialized);

  let database = Database.DBOrd.create () in

  let close_eq =
    if close_equation
    then TermsEq.Ord.close_hyp_modulo_eq
    else (fun restwork r -> restwork r)
  in

  Parsing_helper.debug (fun () ->
    Display.stop_dynamic_display ();
    Parsing_helper.debug_msg "--- Entering solving_request_rule";
    Parsing_helper.debug_msg "Checking clause...";
    Ord.iter_term Terms.check_no_link cl;
    (* History.iter_term_history Terms.check_no_link cl.history; *)
    Parsing_helper.debug_msg "Checking lemmas...";
    List.iter Lemma.Debug.check_lemma lemmas;
    Parsing_helper.debug_msg "Checking successful";
  );

  close_eq (SimplificationRulesOrd.normal_rule_solving database lemmas) cl;

  let liveness_required = requires_liveness () in

  let first_saturation = List.rev (complete_rules_solving database !set_saturated_rules !set_saturated_rules_for_redundant_glob (not liveness_required) lemmas) in

  if liveness_required
  then
    begin 
      let database = Database.DBOrd.create () in
      List.iter (fun cl -> match prepare_clause_for_liveness cl with
        | None -> Database.DBOrd.add_rule database cl
        | Some cl' -> SimplificationRulesOrd.normal_rule_solving database lemmas cl'
      ) first_saturation;
      List.rev (complete_rules_solving database !set_saturated_rules !set_saturated_rules_for_redundant_glob true lemmas)
    end
  else first_saturation

(* Solving other query goals *)

(* Only used in query_goal and query_goal_not. *)
let query_goal_std lemmas g =
  let cl = 
    { 
      Ord.hypotheses = [g,COSpecific [1,Leq],0];
      Ord.conclusion = g;
      Ord.history = Empty(g);
      Ord.constraints = Terms.true_constraints
    }
  in
  solving_request_rule lemmas cl

(* Only used for Horn and typed Horn front-ends *)
let query_goal g =
  match query_goal_std [] g with
  | [] ->
      print_string "RESULT goal unreachable: ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "<span class=\"result\">RESULT <span class=\"trueresult\">goal unreachable</span>: ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.print_string "</span>";
          Display.Html.newline();
        end
  | l ->
      List.iter (fun cl ->
        let rule = Ord.reduction_of cl in
        Display.auto_cleanup_display (fun () ->
          print_string "goal reachable: ";
          Display.Text.display_rule_abbrev rule;
          if !Param.html_output then
            begin
              Display.Html.print_string "goal reachable: ";
              Display.Html.display_rule_abbrev rule
            end;
          begin
            try
              ignore (History.build_history None cl)
            with Not_found -> ()
          end;
          cleanup()
            )
      ) l;
      print_string "RESULT goal reachable: ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "<span class=\"result\">RESULT <span class=\"unknownresult\">goal reachable</span>: ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.print_string "</span>";
          Display.Html.newline();
        end

let query_goal_not lemmas g =
  match query_goal_std lemmas g with
    [] ->
      print_string "ok, secrecy assumption verified: fact unreachable ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "ok, secrecy assumption verified: fact unreachable ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.newline()
        end
  | cl_l ->
      List.iter (fun cl ->
        let rule = Ord.reduction_of cl in
        Display.auto_cleanup_display (fun () ->
          print_string "goal reachable: ";
          Display.Text.display_rule_abbrev rule;
          if !Param.html_output then
            begin
              Display.Html.print_string "goal reachable: ";
              Display.Html.display_rule_abbrev rule
            end;
          begin
            try
              ignore (History.build_history None cl)
            with Not_found -> ()
          end;
          cleanup()
        )
      ) cl_l;

      if !Param.html_output 
      then Display.Html.print_line "Error: you have given a secrecy assumption that I could not verify.";

      (* TO DO close HTML files properly before this error *)
      Parsing_helper.user_error "you have given a secrecy assumption that I could not verify."

(* Main completion. This function:
  1 - applies the first saturation procedure 
  2 - verifies the not declarations
  3 - applies the second saturation procedure if liveness has been activated

  Multiple calls to [solving_request_rule], [query_goal], and [query_goal_std] can be done after that
*)

let completion lemmas clauses =
  Parsing_helper.debug (fun () ->
    Parsing_helper.debug_msg "---- Entering completion";
    Parsing_helper.debug_msg "Checking lemmas...";
    Display.Text.display_list Lemma.Debug.display_lemma "" lemmas;
    List.iter Lemma.Debug.check_lemma lemmas;
    Parsing_helper.debug_msg (Printf.sprintf "Ordered saturation: %b" !ordered_saturation);
    Parsing_helper.debug_msg (Printf.sprintf "Events for second saturation: %s" 
      (String.concat ", " (List.map Display.string_of_fsymb !events_for_second_saturation))
    );
    Parsing_helper.debug_msg (Printf.sprintf "Predicates for second saturation: %s" 
      (String.concat ", " (List.map (fun p -> p.p_name) !predicates_for_second_saturation))
    );
    assert(!current_bound_vars = []);
    Parsing_helper.debug_msg "Checking successful"
  );
  
  let (display_header,display_footer) =
    if !Param.html_output
    then
      begin
        let qs =
          if !is_inside_query then
            "inside" ^ (string_of_int (!Param.inside_query_number))
          else
            (string_of_int (!Param.current_query_number))
        in
        (fun () ->
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/clauses" ^ qs ^ ".html") ("ProVerif: clauses for query " ^ qs);
          Display.Html.print_string "<H1>Initial clauses</H1>\n";
          Display.Html.display_start_list ();
        ), (fun () ->
          Display.Html.display_end_list ();
          Display.LangHtml.close();
          Display.Html.print_string ("<A HREF=\"clauses" ^ qs ^ ".html\" TARGET=\"clauses\">Clauses</A><br>\n")
        )
      end
    else if (!Param.verbose_explain_clauses != Param.NoClauses) || (!Param.explain_derivation = false)
    then
      (fun () ->
        Display.Text.print_string "Initial clauses:";
        Display.Text.display_start_list ()
      ), Display.Text.display_end_list
    else (fun () -> ()), (fun () -> ())
  in

  let display_one_initial_clause rule =
    if !Param.html_output
    then Display.Html.display_rule_num_abbrev rule
    else if (!Param.verbose_explain_clauses != Param.NoClauses) || (!Param.explain_derivation = false)
    then 
      begin 
        Display.stop_dynamic_display ();
        Display.Text.display_rule_num_abbrev rule
      end
  in

  (* Only for Horn and THorn input file. *)
  let complete_with_equations database rulelist =
    print_string "Completing with equations...\n";
    List.iter (fun rule ->
      if !Param.verbose_rules then
        begin
          Display.stop_dynamic_display ();
          print_string "Completing ";
          Display.Text.display_rule_indep rule
        end
      else
        begin
          database.Database.DB.count <- database.Database.DB.count + 1;
          if database.count mod 200 = 0 then
            begin
              Display.stop_dynamic_display ();
              print_string ((string_of_int database.count) ^ " rules completed.");
              Display.Text.newline()
            end
        end;
      let cl = Std.of_reduction rule in 
      let cl' = Terms.auto_cleanup (fun () -> Std.copy cl) in
      TermsEq.Std.close_modulo_eq (SimplificationRules.normal_rule database lemmas) cl'
    ) rulelist;

    Display.stop_dynamic_display ();

    (* Convert the queue of rules into a list, to display it *)
    let rulelisteq =
      let l = ref [] in
      Database.QueueClause.iter (fun (r,_,_) -> l := r::(!l)) database.Database.DB.queue;
      !l
    in
    if !Param.html_output then
      begin
        Display.LangHtml.openfile ((!Param.html_dir) ^ "/eqclosure.html") "ProVerif: clauses completed with equations";
        Display.Html.print_string "<H1>Clauses completed with equations</H1>\n";
        Display.Html.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Html.display_rule_nonewline (Std.reduction_of r))) rulelisteq;
        Display.LangHtml.close();
        Display.Html.print_string "<A HREF=\"eqclosure.html\">Clauses completed with equations</A><br>\n"
      end
    else if !Param.verbose_completed then
      begin
        Display.Text.print_string "Clauses completed with equations:";
        Display.Text.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Text.display_rule_nonewline (Std.reduction_of r))) rulelisteq
      end
  in

  let display_complete display_text display_html completed_cl =
    if !Param.html_output then
      begin
        let qs =
          if !is_inside_query then
            "inside" ^ (string_of_int (!Param.inside_query_number))
          else
            string_of_int (!Param.current_query_number)
        in
        Display.LangHtml.openfile ((!Param.html_dir) ^ "/compclauses" ^ qs ^ ".html") ("ProVerif: completed clauses for query " ^ qs);
        Display.Html.print_string "<H1>Completed clauses</H1>\n";
        Display.Html.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> display_html r)) completed_cl;
        Display.LangHtml.close();
        Display.Html.print_string ("<A HREF=\"compclauses" ^ qs ^ ".html\">Completed clauses</A><br>\n")
      end
    else if !Param.verbose_completed then
      begin
        Display.Text.print_string "Completed clauses:";
        Display.Text.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> display_text r)) completed_cl
      end
  in

  let create_database create_DB convert_rule normal_rule = function
    | Given _ -> Parsing_helper.internal_error __POS__ "Should be handled ealier"
    | ToGenerate(rulelist_attacker,generate_process_rules) ->
        assert (!close_with_equations = false);
        Display.Text.print_line "Translating the process into Horn clauses...";
        (* Reinit the rule database *)
        let database = create_DB () in
        display_header ();
        let display_and_normalise rule =
          Terms.auto_cleanup (fun () ->
            display_one_initial_clause rule;
            convert_rule (fun cl ->
              normal_rule database lemmas cl
            ) rule
          )
        in
        List.iter display_and_normalise rulelist_attacker;
        generate_process_rules display_and_normalise;
        display_footer ();
        database
  in

  let clauses_to_be_generated = function
    | Given _ -> false
    | _ -> true
  in


  let saturated_clauses = 
    if !ordered_saturation && clauses_to_be_generated clauses
	(* We do not want to do ordered saturation in calls to [sound_bad_derivable] from [Piauth],
           in which the clauses are given *)
    then 
      begin
        let first_completed_rules = 
          let database = create_database Database.DBOrd.create Transl_helper.clauseOrd_of_reduction SimplificationRulesOrd.normal_rule clauses in

          Display.stop_dynamic_display ();

          (* Initialize the selection function *)
          Selfun.Ord.initialize_before_saturation database.queue;

          (* Display initial queue *)
          begin match !Param.verbose_base with
          | VBAll
          | VBInterval(0,_) -> Database.DBOrd.display_initial_queue database
          | _ -> ()
          end;

          (* Complete the rule base *)
          print_string "Completing...\n";
          SimplificationRulesOrd.complete_rules database lemmas
        in

        if requires_liveness ()
        then 
          begin 
            Parsing_helper.debug (fun () ->
              display_complete Ord.Text.display_nonewline Ord.Html.display_nonewline first_completed_rules;
            );
            (* Liveness required *)
            print_string "Preparing second saturation...\n";
            let database = Database.DBOrd.create () in
            
            List.iter (fun cl -> match prepare_clause_for_liveness cl with
              | None -> Database.DBOrd.add_rule database cl
              | Some cl' -> SimplificationRulesOrd.normal_rule database lemmas cl'
            ) first_completed_rules;

            Display.stop_dynamic_display ();

            (* Display initial queue *)
            begin match !Param.verbose_base with
            | VBAll
            | VBInterval(0,_) -> Database.DBOrd.display_initial_queue database
            | _ -> ()
            end;
            
            (* Complete the rule base *)
            print_string "Completing...\n";
            let completed_rules = SimplificationRulesOrd.complete_rules database lemmas in

            display_complete Ord.Text.display_nonewline Ord.Html.display_nonewline completed_rules;
            completed_rules
          end
        else
          begin 
            (* No liveness *)
            display_complete Ord.Text.display_nonewline Ord.Html.display_nonewline first_completed_rules;
            first_completed_rules
          end
      end
    else
      begin
        let database = match clauses with
          | Given rulelist ->
            (* Reinit the rule database *)
            let database = Database.DB.create () in
            display_header ();
            List.iter display_one_initial_clause rulelist;
            display_footer ();

            if (!close_with_equations) && (TermsEq.hasEquations())
            then complete_with_equations database rulelist
            else List.iter (fun r -> SimplificationRules.normal_rule database lemmas (Std.of_reduction r)) rulelist;

            database
          | _ -> create_database Database.DB.create Transl_helper.clause_of_reduction SimplificationRules.normal_rule clauses
        in

        Display.stop_dynamic_display ();

        (* Initialize the selection function *)
        Selfun.Std.initialize_before_saturation database.queue;

        (* Display initial queue *)
        begin match !Param.verbose_base with
        | VBAll
        | VBInterval(0,_) -> Database.DB.display_initial_queue database
        | _ -> ()
        end;

        (* Complete the rule base *)
        print_string "Completing...\n";
        let completed_rules = SimplificationRules.complete_rules database lemmas in
        display_complete Std.Text.display_nonewline Std.Html.display_nonewline completed_rules;

        (* Initialise the ordered rules for the base *)
        List.map clauseOrd_of_saturated_clause completed_rules
      end
  in
  
  let sat_rules_for_redundant_glob =
    List.filter (fun sat_cl ->
      List.for_all (fun hyp -> is_unselectable (HypOrd.get_fact hyp)) sat_cl.Ord.hypotheses
    ) saturated_clauses
  in
  saturated_rules := saturated_clauses;
  set_saturated_rules := Database.SetSatClause.of_list saturated_clauses;
  set_saturated_rules_for_redundant_glob := Database.SetSatClause.of_list sat_rules_for_redundant_glob;

  (* Verify the secrecy assumptions *)
  List.iter (query_goal_not lemmas) (!not_set)

(** Initialisation *)

let initialize_elimtrue_set elimtrue_decl =
  elimtrue_set := 
    List.map (fun (i,fact) ->
      (Rule(i, LblClause, [], fact, true_constraints),fact)
             ) elimtrue_decl

let initialize state =
  initialized := true;
  saturated_rules := [];
  set_saturated_rules := Database.SetSatClause.empty;
  set_saturated_rules_for_redundant_glob := Database.SetSatClause.empty;
  not_set := state.h_not;
  initialize_elimtrue_set state.h_elimtrue;
  memberOptim_set := state.h_memberOptim;
  Ordering.initialise_pred_to_prove state.h_pred_prove;
  initialise_useless_events_for_lemmas state.h_event_in_queries state.h_lemmas;
  initialize_equiv_set state.h_equiv;
  Selfun.initialize state.h_nounif state.h_solver_kind;
  List.iter (fun r -> ignore (Selfun.Std.selection_fun (Std.of_reduction r))) state.h_clauses_to_initialize_selfun;
  Weaksecr.initialize state.h_solver_kind;
  Noninterf.initialize state.h_solver_kind;
  Database.FeatureGenClause.initialize ();
  Database.FeatureGenOrdClause.initialize ();

  predicates_for_second_saturation := state.h_predicates_for_second_saturation;
  events_for_second_saturation := state.h_events_for_second_saturation;

  is_equivalence_query := (state.h_solver_kind = Solve_Equivalence);
  begin 
    match state.h_solver_kind with
    | Solve_Equivalence ->
        (* We may want to always put an ordered saturation when working on equivalence 
           with axioms for convergent bitraces. To test. *)
	ordered_saturation := state.h_lemmas <> [] || !Param.ordered_saturation
(*   | Solve_CorrespBipro ->
        (* We are proving a lemma on bitrace *)
        ordered_saturation := true  *) [@ppwarning "Vincent: is that code useful?"]
    | _ ->
        (* Standard *)
        ordered_saturation := state.h_ordered_saturation || !Param.ordered_saturation
  end;

  (* This assertions aims to check that equations have already been
     recorded *)
  assert ((state.h_equations != []) = (TermsEq.hasEquations()));
  close_with_equations := state.h_close_with_equations;

  (* Display all lemmas *)
  if state.h_lemmas != []
  then
    begin
      if !Param.html_output then
        begin
          let qs =
            if !is_inside_query then
              "inside" ^ (string_of_int (!Param.inside_query_number))
            else
              (string_of_int (!Param.current_query_number))
          in
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/lemmas" ^ qs ^ ".html") ("ProVerif: lemmas for the verification of query " ^ qs);
          Display.Html.print_string "<H1>Lemmas</H1>\n";
          Display.Html.display_lemmas state.h_lemmas;
          Display.LangHtml.close();
          Display.Html.print_string ("<A HREF=\"lemmas" ^ qs ^ ".html\" TARGET=\"lemmas\">Lemmas</A><br>\n")
        end
      else if !Param.verbose_lemmas || not !Param.explain_derivation then
        begin
          Display.Text.print_string "Lemmas used in the verification of the query:";
          Display.Text.display_lemmas state.h_lemmas
        end
    end

(* Initialisation for correspondence queries *)

let corresp_initialize state =
  (* May be used also for correspondence queries
     on biprocesses, so with Solve_CorrespBipro as well *)
  initialize state;

  (* We gather the lemmas *)
  let lemmas = List.filter (fun lem -> lem.l_sat_app) state.h_lemmas in

  completion lemmas state.h_clauses


(* We allow subsequent calls to resolve_hyp, query_goal_std,
  sound_bad_derivable after this initialization and completion *)

let reset () =
  sound_mode := false;
  initialized := false;
  is_inside_query := false;
  close_with_equations := false;

  predicates_for_second_saturation := [];
  events_for_second_saturation := [];
  ordered_saturation := false;

  is_equivalence_query := false;

  initialize_equiv_set [];
  not_set := [];
  elimtrue_set := [];

  events_only_for_lemmas := [];
  events_only_for_lemmas_without_options := [];
  all_original_lemmas := [];

  Selfun.initialize [] Solve_Standard;
  Weaksecr.initialize Solve_Standard;
  Noninterf.initialize Solve_Standard;

  saturated_rules := [];
  set_saturated_rules := Database.SetSatClause.empty;
  set_saturated_rules_for_redundant_glob := Database.SetSatClause.empty;
  
  Ordering.reset_pred_to_prove ()
  
let internal_bad_derivable lemmas rulelist =
  completion lemmas rulelist;
  List.filter (fun cl -> match cl.Ord.conclusion with
    | Pred(p,[]) when p == Param.bad_pred -> true
    | _ -> false
  ) !saturated_rules

(* Test whether bad is derivable from rulelist;
   this function does not alter saturated_rules, so that it can be called
   even if I am calling query_goal_std afterwards to test whether some fact
   is derivable from other completed clauses.
   Furthermore, it is guaranteed to say that that bad is derivable only
   if it is actually derivable *)
let sound_bad_derivable rulelist =
  assert (!initialized);
  (* Saving parameters *)
  let old_saturated_rules = !saturated_rules in
  let old_set_sat_rules = !set_saturated_rules in
  let old_set_sat_rules_glob = !set_saturated_rules_for_redundant_glob in
  let old_sound_mode = !sound_mode in
  is_inside_query := true;
  sound_mode := true;

  let r = internal_bad_derivable [] (Given rulelist) in

  (* Restore parameters *)
  is_inside_query := false;
  sound_mode := old_sound_mode;
  saturated_rules :=  old_saturated_rules;
  set_saturated_rules := old_set_sat_rules;
  set_saturated_rules_for_redundant_glob := old_set_sat_rules_glob;
  
  r

let bad_derivable state =
  assert (state.h_solver_kind <> Solve_Standard);
  initialize state;
  (* We gather the lemmas *)
  let lemmas =
    List.fold_left (fun acc_l lem ->
      if lem.l_sat_app
      then
        begin
          if lem.l_induction <> None
          then Parsing_helper.internal_error __POS__ "[Rules.bad_derivable] There should not be any inductive lemma when proving equivalence.";
          (lem::acc_l)
        end
      else acc_l
    ) [] state.h_lemmas
  in
  let r = internal_bad_derivable lemmas state.h_clauses in
  reset();
  r

let bad_in_saturated_database () =
  List.exists (fun cl -> match cl.Ord.conclusion with
    | Pred(p,[]) when p == Param.bad_pred -> true
    | _ -> false
  ) !saturated_rules

let bad_in_saturated_database_opt () =
  List.find_opt (fun cl -> match cl.Ord.conclusion with
    | Pred(p,[]) when p == Param.bad_pred -> true
    | _ -> false
  ) !saturated_rules

let main_analysis state goal_set =
  assert (state.h_solver_kind = Solve_Standard);
  initialize state;
  completion [] state.h_clauses;
  List.iter query_goal goal_set;
  reset()

(* Check whether hypothesis of the clause is unsatifiable *)

exception Satisfiable

let is_hypothesis_unsatisfiable cl =
  assert (!Terms.current_bound_vars == []);

  let rec apply_normal_rule cl =
    SimplificationRulesOrd.simp_eq_rule (
      SimplificationRulesOrd.simplify_constraints (fun _ -> raise Satisfiable) apply_normal_rule
    ) cl
  in

  try
    apply_normal_rule cl;
    true
  with Satisfiable -> false  
