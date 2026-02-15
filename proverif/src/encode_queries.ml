open Types
open Pitypes
open Utils

let apply_encode_step new_def p = function
  | Public_vars (l) ->
      begin
        try
          let (_,pub_ch) = List.find (fun (v, _) -> Terms.equal_terms new_def v) l in
          Output(FunApp(pub_ch, []), new_def, p, Terms.new_occurrence())
        with Not_found ->
          p
      end
  | Secret_reach(l, ev) ->
      if List.exists (Terms.equal_terms new_def) l then
        Event(FunApp(ev, [new_def]), (None, Stringmap.StringMap.empty),
              p, Terms.new_occurrence())
      else
        p
  | Secret_ror(l, pub_ch) ->
      if List.exists (Terms.equal_terms new_def) l then
        let ty = Terms.get_term_type new_def in
        let rand = Terms.create_name ~orig:false "rand" (Param.tmp_type, ty) true in
        Restr(rand, (None, Stringmap.StringMap.empty),
              Output(FunApp(pub_ch, []),
                     Terms.make_choice new_def (FunApp(rand, [])), p,
                     Terms.new_occurrence()),
              Terms.new_occurrence())
      else
        p

let apply_encode_steps new_def p step_list =
  List.fold_left (apply_encode_step new_def) p step_list

let apply_encode_vars vars p1 step_list =
  List.fold_left (fun p v ->
    apply_encode_steps (Var v) p step_list
      ) p1 vars

let rec encode_process step_list = function
    Nil -> Nil
  | Par(p1,p2) ->
      Par(encode_process step_list p1,
          encode_process step_list p2)
  | Repl(p,occ) ->
      Repl(encode_process step_list p, occ)
  | Restr(f, new_args, p, occ) ->
      let new_def = FunApp(f, []) in
      let p1 = encode_process step_list p in
      let p2 = apply_encode_steps new_def p1 step_list in
      Restr(f, new_args, p2, occ)
  | Test(t, p1, p2, occ) ->
      Test(t, encode_process step_list p1, encode_process step_list p2, occ)
  | Input(ch, pat, p, occ) ->
      let vars = Terms.get_vars_acc_pat [] pat in
      let p1 = encode_process step_list p in
      let p2 = apply_encode_vars vars p1 step_list in
      Input(ch, pat, p2, occ)
  | Output(ch, t, p, occ) ->
      Output(ch, t, encode_process step_list p, occ)
  | Let(pat, t, p1, p2, occ) ->
      let vars = Terms.get_vars_acc_pat [] pat in
      let p1' = encode_process step_list p1 in
      let p1'' = apply_encode_vars vars p1' step_list in
      let p2' = encode_process step_list p2 in
      Let(pat, t, p1'', p2', occ)
  | LetFilter(vars, f, p1, p2, occ) ->
      let p1' = encode_process step_list p1 in
      let p1'' = apply_encode_vars vars p1' step_list in
      let p2' = encode_process step_list p2 in
      LetFilter(vars, f, p1'', p2', occ)
  | Event(t, new_args, p, occ) ->
      Event(t, new_args, encode_process step_list p, occ)
  | Insert(t, p, occ) ->
      Insert(t, encode_process step_list p, occ)
  | Get(pat, t, p1, p2, occ) ->
      let vars = Terms.get_vars_acc_pat [] pat in
      let p1' = encode_process step_list p1 in
      let p1'' = apply_encode_vars vars p1' step_list in
      let p2' = encode_process step_list p2 in
      Get(pat, t, p1'', p2', occ)
  | Phase(n, p, occ) ->
      Phase(n, encode_process step_list p, occ)
  | Barrier(n, tag, p, occ) ->
      Barrier(n, tag, encode_process step_list p, occ)
  | AnnBarrier _ ->
      Parsing_helper.internal_error __POS__ "Annotated barriers should not appear in encode_process"
  | NamedProcess(s, tl, p) ->
      NamedProcess(s, tl, encode_process step_list p)

let encode_process step_list p =
  Simplify.reset_occurrence (encode_process step_list p)

(* Treat temporal correspondence queries *)

(* Transforming a correspondence query containing temporal conditions follows the following steps:
  1. Adds a fresh occurrence variable and a temporal variable to every event and fact when
      there is none.
  2. Transform the query into a DNF without nested query. The nested queries are replaced
      by a conjunction of facts and by adding temporal constraints.
  3. For each disjunct, we look at all i < max(i1,..,in) and see if there is another constraint already 
     implying the inequality. Yes so we remove it or we apply case distinction.
  4. For each disjunct, we gather the temporal conditions and simplify them. To do so, we transform
      them into a conjunction of constraints on natural numbers and use the associated
      simplification functions.
  5. Transform each conjunction using ordering functions, equalities, and inequalities on occurrence
      variables and individual nested queries
  6. Cleanup the query, i.e., remove the temporal variables and remove the occurrence variables that
      are not used in the constraints.
*)

(* 1. Adding fresh occurrences and temporal variables *)

let add_fresh_occ_at_event = function
  | QSEvent(inj,ord_data,occ,ev) ->
      assert(occ = None);
      let occ' = Some (Terms.new_var_def_term Param.occurrence_type) in
      let ord_data' = match ord_data.temp_var with
        | Some _ -> ord_data
        | _ -> { ord_data with temp_var = Some (Terms.new_var_def_term Param.time_type, Parsing_helper.dummy_ext) }
      in
      QSEvent(inj,ord_data',occ',ev)
  | QSEvent2 _ -> Parsing_helper.internal_error __POS__ "[add_fresh_occ_at_event] Bievent should not occur here."
  | QFact(p,ord_data,args) ->
      let ord_data' = match ord_data.temp_var with
        | Some _ -> ord_data
        | _ -> { ord_data with temp_var = Some (Terms.new_var_def_term Param.time_type, Parsing_helper.dummy_ext) }
      in
      QFact(p,ord_data',args)
  | ev -> ev

let rec add_fresh_occ_at_concl_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints _ as q -> q (* no occ in constraints *)
  | QEvent ev -> QEvent(add_fresh_occ_at_event ev)
  | NestedQuery(Before([e],concl)) -> NestedQuery(Before([add_fresh_occ_at_event e],add_fresh_occ_at_concl_query concl))
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[add_fresh_occ_at_concl_query] Nested queries should contain a single event as premise."
  | QAnd(concl1,concl2) -> QAnd(add_fresh_occ_at_concl_query concl1,add_fresh_occ_at_concl_query concl2)
  | QOr(concl1,concl2) -> QOr(add_fresh_occ_at_concl_query concl1,add_fresh_occ_at_concl_query concl2)

let add_fresh_occ_at_realquery = function
  | Before(evl,concl) -> Before(List.map add_fresh_occ_at_event evl,add_fresh_occ_at_concl_query concl)

(* 2. Gather the query into a DNF *)

let get_at_term = function
  | QSEvent(_,{ temp_var = Some at; },_,_)
  | QFact(_,{ temp_var = Some at; },_ ) -> at
  | _ -> Parsing_helper.internal_error __POS__ "[get_at_term] The events should contain a time variable by now."

let check_distinct_time_var evl1 evl2 =
  List.iter (fun ev -> List.iter (fun ev' ->
    let (t, ext) = get_at_term ev in
    let (t', ext') = get_at_term ev' in
    if Terms.equal_terms t t'
    then
      let (ext0, line0) =
        match Parsing_helper.get_extent true ext, Parsing_helper.get_extent true ext' with
        | (_, None) -> (ext, "")
        | (None, Some _) -> (ext', "")
        | (Some _, Some s) -> (ext, "Time variable also assigned at "^s^".\n")
      in
      let line1 = "In a correspondence query E ==> H, a fact/event of E and a different fact/event from H or E cannot be assigned the same time variable.\n" in
      let line2 = "Moreover, when considering H in its disjunctive normal form (i.e. H equivalent to H_1 || ... || H_n), two facts or events of the same disjunct H_i cannot be assigned the same time variable" in
      Parsing_helper.input_error (line0^line1^line2) ext0
        ) evl2) evl1

let rec check_distinct_time_var_premises = function
  | [] -> ()
  | ev::q ->
      check_distinct_time_var_premises q;
      check_distinct_time_var [ev] q

let check_assigned_time evl time_constr =
  let check (t,ext) =
    if not (List.exists (fun ev -> Terms.equal_terms t (fst (get_at_term ev))) evl) then
      Parsing_helper.input_error "Time variable not assigned. In a correspondence query E ==> H, when considering H in its disjunctive normal form (i.e. H equivalent to H_1 || ... || H_n), any time variable occurring in a disjunct should be assigned by a fact in the same disjunct or in E" ext
  in
  List.iter (function
    | QNeq(t1,t2) | QEq(t1,t2) | QGeq(t1,t2) | QGr(t1,t2) ->
        check t1; check t2
    | _ -> ()
  ) time_constr

(* [f_next] takes three lists as arguments.
  - List of events and facts
  - List of temporal constraints
  - List of other constraints *)
let disjunct_normal_form_event f_next nested_op = function
  | (QSEvent(_,{ temp_var = Some at ;_ },_,_) | QFact(_,{ temp_var = Some at ;_ },_)) as ev ->
      begin match nested_op with
        | None -> f_next [ev] [] []
        | Some at' -> f_next [ev] [QGeq(at',at)] []
      end
  | QSEvent _ | QFact _ -> Parsing_helper.internal_error __POS__ "[disjunct_normal_form_event] Queries should contain temporal variable by now."
  | QSEvent2 _ -> Parsing_helper.internal_error __POS__ "[disjunct_normal_form_event] Queries on biprocess should not be encoded as they do not contain temporal variable."
  | (QNeq((t,_),_) | QEq((t,_),_) | QGeq((t,_),_) | QGr((t,_),_)) as constr when Terms.get_term_type t == Param.time_type -> f_next [] [constr] []
  | (QMax (t,_) | QMaxq (t,_)) as constr ->
      assert(Terms.get_term_type t == Param.time_type);
      f_next [] [constr] []
  | ev -> f_next [] [] [ev]

let rec disjunct_normal_form_concl_query f_next nested_op = function
  | QConstraints cons -> f_next [] [] [] cons
  | QTrue -> f_next [] [] [] Terms.true_constraints
  | QFalse -> ()
  | QEvent ev -> disjunct_normal_form_event (fun evl1 atl1 constrl1 -> f_next evl1 atl1 constrl1 Terms.true_constraints) nested_op ev  
  | NestedQuery(Before([QSEvent(_,{ temp_var = at; _},_,_) as ev],concl)) ->
      disjunct_normal_form_concl_query (fun evl1 atl1 constrl1 cons1 ->
        disjunct_normal_form_event (fun evl2 atl2 constrl2 ->
          check_distinct_time_var evl1 evl2;
          f_next (evl2@evl1) (atl2@atl1) (constrl2@constrl1) cons1
        ) nested_op ev
      ) at concl
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[disjunct_normal_form_concl_query] Nested queries should contain a single event as premise."
  | QAnd(concl1,concl2) ->
      disjunct_normal_form_concl_query (fun evl1 atl1 constrl1 cons1 ->
        disjunct_normal_form_concl_query (fun evl2 atl2 constrl2 cons2 ->
          check_distinct_time_var evl1 evl2;
          f_next (evl1@evl2) (atl1@atl2) (constrl1@constrl2) (Terms.wedge_constraints cons1 cons2)
        ) nested_op concl2
      ) nested_op concl1
  | QOr(concl1,concl2) ->
      disjunct_normal_form_concl_query f_next nested_op concl1;
      disjunct_normal_form_concl_query f_next nested_op concl2

(* 4. Simplification of Max and Maxq *)

(* [is_QMaxq_implied] checks if the constraint [i <= max(i_l)] is implied by [std_temp_c] *)
let is_QMaxq_implied i i_l std_temp_c = 
  List.exists (function
    | QGeq((i1,_),(i2,_))
    | QGr((i1,_),(i2,_)) -> Terms.equal_terms i2 i && List.exists (Terms.equal_terms i1) i_l
    | QEq((i1,_),(i2,_)) -> 
        (Terms.equal_terms i2 i && List.exists (Terms.equal_terms i1) i_l) ||
        (Terms.equal_terms i1 i && List.exists (Terms.equal_terms i2) i_l)
    | _ -> false
  ) std_temp_c

(* [is_QMax_implied] checks if the constraint [i < max(i_l)] is implied by [std_temp_c] *)
let is_QMax_implied i i_l std_temp_c = 
  List.exists (function
    | QGr((i1,_),(i2,_)) -> Terms.equal_terms i2 i && List.exists (Terms.equal_terms i1) i_l
    | _ -> false
  ) std_temp_c


[@ppwarning "Vincent: why do you need to simplify QMax, QMaxq? You do not allow them in input; you have the max in the orderings (QOMax)."]
    
let simplify_maximal_temporal_constraints f_next at_constra =

  let max_c, std_c = List.partition (function QMax _ | QMaxq _ -> true | _ -> false) at_constra in

  let rec explore acc_std_c = function
    | [] -> f_next acc_std_c
    | QMax(i,i_l)::q ->
        if is_QMax_implied i i_l acc_std_c
        then explore acc_std_c q
        else
          List.iter (fun i' ->
            explore (QGr((i',Parsing_helper.dummy_ext),(i,Parsing_helper.dummy_ext)) :: acc_std_c) q
          ) i_l 
    | QMaxq(i,i_l)::q ->
        if is_QMaxq_implied i i_l acc_std_c
        then explore acc_std_c q
        else
          List.iter (fun i' ->
            explore (QGeq((i',Parsing_helper.dummy_ext),(i,Parsing_helper.dummy_ext)) :: acc_std_c) q
          ) i_l 
    | _ -> Parsing_helper.internal_error __POS__ "[simplify_maximal_temporal_constraints] Unexpected constraints"
  in

  explore std_c max_c

(* 4. Simplification of temporal constraints *)

let simplify_temporal_constraints ?(id_thread=0) at_constr =
  let mapping = ref [] in
  let is_NoLink lst = match lst.(id_thread) with NoLink -> true | _ -> false in
  let is_VLink lst = match lst.(id_thread) with VLink _ -> true | _ -> false in
  let assoc_new_var (t, ext) = match t with
    | Var ({ link = lst; _ } as v) when (is_NoLink lst) ->
        let v_nat = Terms.new_var_def Param.nat_type in
        (v.link).(id_thread) <- VLink v_nat;
        mapping := (v_nat,(v,ext)) :: !mapping;
        Var v_nat
    | Var ({ link = lst; _}) when (is_VLink lst) -> let VLink v_nat = lst.(id_thread) in Var v_nat
    | _ -> Parsing_helper.internal_error __POS__ "[simplify_temporal_constraints] Temporal term should be variables."
  in

  let eq_list = ref [] in

  let nat_constr =
    List.fold_left (fun acc q_at -> match q_at with
      | QNeq(i,j) ->
          let i_nat = assoc_new_var i in
          let j_nat = assoc_new_var j in
          { acc with neq = [i_nat,j_nat] :: acc.neq }
      | QEq(i,j) ->
          let i_nat = assoc_new_var i in
          let j_nat = assoc_new_var j in
          eq_list := (i_nat,j_nat) :: !eq_list;
          acc
      | QGeq(i,j) ->
          let i_nat = assoc_new_var i in
          let j_nat = assoc_new_var j in
          { acc with geq = (i_nat,0,j_nat) :: acc.geq }
      | QGr(i,j) ->
          let i_nat = assoc_new_var i in
          let j_nat = assoc_new_var j in
          { acc with geq = (i_nat,-1,j_nat) :: acc.geq }
      | _ -> Parsing_helper.internal_error __POS__ "[simplify_temporal_constraints] Unexpected case."
    ) Terms.true_constraints at_constr
  in

  let vars_to_preserve = List.map (fun (v_nat,_) -> v_nat) !mapping in

  List.iter (fun (_,(v,_)) -> (v.link).(id_thread) <- NoLink) !mapping;

  (* We simplify the constraints *)
  let (eq_list',nat_constr') =
    Terms.auto_cleanup (fun () ->
      List.iter (fun (t1,t2) -> Terms.unify t1 t2) !eq_list;
      let nat_constr1 = Terms.copy_constra4 nat_constr in
      let get_vars_op = Some (fun () -> vars_to_preserve) in
      TermsEq.simplify_constraints_continuation get_vars_op (fun nat_constr2 ->
        (* No new equality *)
        (!eq_list,nat_constr2)
      ) (fun nat_constr2 ->
        let eq_list' =
          List.fold_left (fun acc v -> match (v.link).(id_thread) with
            | NoLink -> acc
            | TLink _ -> (Var v,Terms.copy_term4 (Var v)) :: acc
            | _ -> Parsing_helper.internal_error __POS__ "[simplify_temporal_constraints] Unexpected link."
          ) [] vars_to_preserve
        in
        (eq_list',nat_constr2)
      ) nat_constr1
    )
  in

  let apply_mapping = function
    | Var v -> let (v, ext) = List.assq v !mapping in Var v, ext
    | _ -> Parsing_helper.internal_error __POS__ "[simplify_temporal_constraints] Unexpected term."
  in

  let at_eq_list = List.map (fun (t1,t2) -> apply_mapping t1, apply_mapping t2) eq_list' in
  let at_ineq_list =
    List.map (fun (t,i,t') -> match i with
      | -1 -> QGr(apply_mapping t,apply_mapping t')
      | 0 -> QGeq(apply_mapping t,apply_mapping t')
      | _ ->
        (* The simplification algorithm and the fact that all (strict) inequalities only contain variables ensure that the simplified
           constraint also only contains (strict) inequalities between variables. *)
        Parsing_helper.internal_error __POS__ "[simplify_temporal_constraints] The simplified constraints should contain only inequalities between variables"
    ) nat_constr'.geq
  in
  let at_neq_list =
    List.map (function
      | [i,j] -> apply_mapping i, apply_mapping j
      | _ ->
        (* We only have disequalities between variables  *)
        Parsing_helper.internal_error __POS__ "[simplify_temporal_constraints] The simplified constraints should contain only disequalities between variables"
    ) nat_constr'.neq
  in
  (at_eq_list,at_neq_list,at_ineq_list)

(* 5. Transformation of the query *)

type event_info =
  {
    event : Pitypes.event;
    inst : int ref;
    keep_occ : bool ref;
  }

let generate_query_event ev_info = match ev_info.event with
  | QSEvent(inj,ord_data,occ,ev) ->
      if !(ev_info.keep_occ)
      then QSEvent(inj,{ ord_data with temp_var = None },occ,ev)
      else QSEvent(inj,{ ord_data with temp_var = None },None,ev)
  | QFact(p,ord_data,args) -> QFact(p,{ ord_data with temp_var = None },args)
  | _ -> Parsing_helper.internal_error __POS__ "[generate_query_event] Unexpected query event."

let get_occ_term = function
  | QSEvent(_,_,Some occ,_) -> occ
  | _ -> Parsing_helper.internal_error __POS__ "[get_occ_term] Events should have occurrence by now."

let get_premises_order prem_info at =
  let rec aux n = function
      [] -> Parsing_helper.internal_error __POS__ "[get_premises_order] at term not found"
    | ev_info :: rest ->
	if Terms.equal_terms (fst (get_at_term ev_info.event)) at then
	  n
	else
	  aux (n+1) rest
  in
  aux 1 prem_info

let get_ord_fun = function
  | QSEvent(_,ord_data,_,_) 
  | QFact(_,ord_data,_) -> ord_data
  | _ -> Parsing_helper.internal_error __POS__ "[get_ord_fun] Unexpected query event."

let replace_ord_fun eord_fun = function
  | QSEvent(inj,ord_data,occ,ev) -> QSEvent(inj,{ ord_data with ord_target = eord_fun },occ,ev)
  | QFact(p,ord_data,args) ->  QFact(p,{ ord_data with ord_target = eord_fun },args)
  | _ -> Parsing_helper.internal_error __POS__ "[replace_ord_fun] Unexpected query event."

let remove_injectivity = function
  | QSEvent(inj,ord_fun,occ,ev) -> QSEvent(None,ord_fun,occ,ev)
  | ev -> ev

let is_event = function
  | QSEvent _ -> true
  | _ -> false

let are_comparable ev1 ev2 = match ev1,ev2 with
  | QSEvent(_,_,_,FunApp(e1,_)), QSEvent(_,_,_,FunApp(e2,_)) -> e1 == e2
  | _ -> false

(* For now we don't try to have a representation with several levels of nested queries.
  Improve in the future if it reduces the efficiency or results
*)
let transform_conclusion_query prem_info evl eql neql ineql =

  (* We generate new event info elements for the events in the conclusion *)
  let ev_info_l = List.map (fun ev -> { event = ev; inst = ref 0; keep_occ = ref false }) evl in
  let all_info = prem_info @ ev_info_l in

  let (prem_greater,concl_greater) =
    List.partition (function
      | QGeq((at,_),_) | QGr((at,_),_) -> List.exists (fun ev_info -> Terms.equal_terms (fst (get_at_term ev_info.event)) at) prem_info
      | _ -> false
    ) ineql
  in

  (* We first add the fact @i from the premise in fact_l such that there exists
     a constraint @k > @i or @k >= @i for some k. @k can come from a premise or fact_l *)
  let extended_ev_info_l_1 =
    List.fold_left (fun acc ev_info ->
      let at = fst (get_at_term ev_info.event) in
      let ext_op = 
        List.find_map (function 
          | QGeq(_,(at',ext)) | QGr(_,(at',ext)) -> 
              if Terms.equal_terms at at'
              then Some ext
              else None
          | _ -> None
        ) ineql
      in
      match ext_op with
        | None -> acc
        | Some ext ->
            begin match ev_info.event with 
              | QSEvent _ | QSEvent2 _ -> ()
              | _ -> 
                Parsing_helper.input_error
		  ("When an inequality i > j or i >= j occurs in the conclusion of a query, lemma, or restriction, with i and j time variables associated to facts F and G respectively, the following two conditions must hold:\n"^
		   "1) F@i occurs in the premise or F is an event;\n"^
		   "2) G@j occurs in the conclusion or G is an event.\n"^
		   "Here, G@j occurs in the premise and G is not an event.")
                  ext
            end;
            ev_info.keep_occ := true;
            { ev_info with event = remove_injectivity ev_info.event; inst = ref 0 }::acc
    ) ev_info_l prem_info
  in

  (* We now add the ordering functions *)
  let extended_ev_info_l_2 =
    List.map (fun ev_info ->
      let at_ev = fst (get_at_term ev_info.event) in
      let ord_fun =
        List.fold_left (fun acc -> function
          | QGeq((at_prem,_),(at_ev',_)) when Terms.equal_terms at_ev at_ev' ->
              let i = get_premises_order prem_info at_prem in
              Ordering.intersection_query acc (QOSpecific [(i,(SemStd,Leq))])
          | QGr((at_prem,_),(at_ev',_)) when Terms.equal_terms at_ev at_ev' ->
              let i = get_premises_order prem_info at_prem in
              Ordering.intersection_query acc (QOSpecific [(i,(SemStd,Less))])
          | _ -> acc
        ) (get_ord_fun ev_info.event).ord_target prem_greater
      in
      { ev_info with event = replace_ord_fun ord_fun ev_info.event }
    ) extended_ev_info_l_1
  in

  (* We add the nested queries (corresponding to the case where an element of the conclusion
     appears greater than some other element in the inequalities). *)

  let nested_queries = ref [] in
  let constraint_occ = ref QTrue in

  let rec add_in_nested_queries ev_info ev_info' = function
    | [] ->
        incr ev_info.inst;
        incr ev_info'.inst;
        [ev_info,[ev_info']]
    | (ev_info'',concl)::q when ev_info.event == ev_info''.event ->
        incr ev_info'.inst;
        (ev_info'',ev_info'::concl)::q
    | nested::q -> nested::(add_in_nested_queries ev_info ev_info' q)
  in

  let find at l =
    List.find (fun ev_info -> Terms.equal_terms at (fst (get_at_term ev_info.event))) l
  in

  List.iter (function
    | QGeq((at1,ext1),(at2,_)) ->
        let ev_info1 = find at1 extended_ev_info_l_2 in
        let ev_info2 = find at2 extended_ev_info_l_2 in
        if not (is_event ev_info1.event)
        then Parsing_helper.input_error
	    ("When an inequality i > j or i >= j occurs in the conclusion of a query, lemma, or restriction, with i and j time variables associated to facts F and G respectively, the following two conditions must hold:\n"^
	     "1) F@i occurs in the premise or F is an event;\n"^
	     "2) G@j occurs in the conclusion or G is an event.\n"^
	     "Here, F@i occurs in the conclusion and F is not an event.")
	    ext1;
        nested_queries := add_in_nested_queries ev_info1 ev_info2 !nested_queries
    | QGr((at1, ext1),(at2, ext2)) ->
        let ev_info1 = find at1 extended_ev_info_l_2 in
        let ev_info2 = find at2 extended_ev_info_l_2 in
        if not (is_event ev_info1.event)
        then Parsing_helper.input_error
	    ("When an inequality i > j or i >= j occurs in the conclusion of a query, lemma, or restriction, with i and j time variables associated to facts F and G respectively, the following two conditions must hold:\n"^
	     "1) F@i occurs in the premise or F is an event;\n"^
	     "2) G@j occurs in the conclusion or G is an event.\n"^
	     "Here, F@i occurs in the conclusion and F is not an event.")
	    ext1;
        nested_queries := add_in_nested_queries ev_info1 ev_info2 !nested_queries;
        if are_comparable ev_info1.event ev_info2.event
        then
          begin
            constraint_occ := Reduction_helper.make_qand
		 (QEvent(QNeq((get_occ_term ev_info1.event, ext1),(get_occ_term ev_info2.event, ext2)))) (!constraint_occ);
            ev_info1.keep_occ := true;
            ev_info2.keep_occ := true
          end
    | _ -> Parsing_helper.internal_error __POS__ "[transform_query] Unexpected constraints."
  ) concl_greater;

  (* Gather the events not occurring in the nested queries and also
     indicate if we need to keep the occurrence variables for the others. *)
  let ev_info_not_occurring_in_nested_queries =
    List.fold_left (fun acc ev_info ->
      if !(ev_info.inst) = 0
      then (ev_info::acc)
      else
        begin
          if !(ev_info.inst) > 1
          then ev_info.keep_occ := true;
          acc
        end

    ) [] extended_ev_info_l_2
  in

  (* We go through disequalities *)
  List.iter (fun ((at1,ext1),(at2,ext2)) ->
    let ev_info1 = find at1 all_info in
    let ev_info2 = find at2 all_info in
    if not (is_event ev_info1.event)
    then Parsing_helper.input_error "In the conclusion of a query of the form F@i && G@k && i <> k, F and G must necessarily be events." ext1;
    if not (is_event ev_info2.event)
    then Parsing_helper.input_error "In the conclusion of a query of the form F@i && G@k && i <> k, F and G must necessarily be events." ext2;
    if are_comparable ev_info1.event ev_info2.event
    then
      begin
        ev_info1.keep_occ := true;
        ev_info2.keep_occ := true;
        constraint_occ := Reduction_helper.make_qand
             (QEvent(QNeq((get_occ_term ev_info1.event, ext1),(get_occ_term ev_info2.event, ext2)))) (!constraint_occ)
      end
  ) neql;

  (* We go through equalities *)
  List.iter (fun ((at1, ext1),(at2, ext2)) ->
    let ev_info1 = find at1 all_info in
    let ev_info2 = find at2 all_info in
    if not (is_event ev_info1.event)
    then Parsing_helper.input_error "In the conclusion of a query of the form F@i && G@k && i = k, F and G must necessarily be events." ext1;
    if not (is_event ev_info2.event)
    then Parsing_helper.input_error "In the conclusion of a query of the form F@i && G@k && i = k, F and G must necessarily be events." ext2;
    if not (are_comparable ev_info1.event ev_info2.event)
    then raise TermsEq.FalseConstraint;
    ev_info1.keep_occ := true;
    ev_info2.keep_occ := true;
    constraint_occ := Reduction_helper.make_qand
	 (QEvent(QEq((get_occ_term ev_info1.event, ext1),(get_occ_term ev_info2.event, ext2)))) (!constraint_occ)
  ) eql;

  (* We cleanup the non-necessary occurrences and generate the conclusion query *)
  let concl_q_1 = List.fold_left (fun acc ev_info -> Reduction_helper.make_qand acc (QEvent (generate_query_event ev_info))) QTrue ev_info_not_occurring_in_nested_queries in
  let concl_q_2 =
    List.fold_left (fun acc (ev_info_prem,ev_info_concl) ->
      let concl_nested = List.fold_left (fun acc_concl ev_info -> Reduction_helper.make_qand acc_concl (QEvent (generate_query_event ev_info))) QTrue ev_info_concl in
      let nested = NestedQuery (Before([generate_query_event ev_info_prem],concl_nested)) in
      Reduction_helper.make_qand acc nested
    ) concl_q_1 !nested_queries
  in
  Reduction_helper.make_qand concl_q_2 (!constraint_occ)

(* The main function *)

let encode_temporal_realquery ?(id_thread=0) query =
  let Before(full_premises,concl) = add_fresh_occ_at_realquery query in
  let (premises,constra_prem) = List.partition (function QSEvent _ | QFact _ -> true | _ -> false) full_premises in
  check_distinct_time_var_premises premises;

  let premises_info = List.map (fun ev -> { event = ev; inst = ref 0; keep_occ = ref false }) premises in
  let acc_new_concl = ref QFalse in

  (* We split in disjunctive normal form *)
  disjunct_normal_form_concl_query (fun evl at_constr other_constr cons ->
    simplify_maximal_temporal_constraints (fun at_constr ->
      check_distinct_time_var premises evl;
      check_assigned_time (premises@evl) at_constr;
      try
        let (eql,neql,ineql) = simplify_temporal_constraints ~id_thread:id_thread at_constr in
        let concl_query = transform_conclusion_query premises_info (List.rev evl) eql neql ineql in
        let concl_query' = List.fold_left (fun acc constr -> Reduction_helper.make_qand acc (QEvent constr)) concl_query  other_constr in
        let concl_query'' = 
          if Terms.is_true_constraints cons
          then concl_query'
          else Reduction_helper.make_qand concl_query' (QConstraints cons)
        in
        acc_new_concl := Reduction_helper.make_qor !acc_new_concl concl_query''
      with TermsEq.FalseConstraint -> ()
    ) at_constr
  ) None concl;

  let premises' = List.map generate_query_event premises_info in
  Before(premises'@constra_prem,!acc_new_concl)

let encode_temporal_realquery_e ?(id_thread=0) ext query =
  let query' = encode_temporal_realquery ~id_thread:id_thread query in
  match query' with
    | Before(prem,concl) -> 
        let (att_idx_prem,_) = 
          List.fold_left (fun (acc,i) ev -> match ev with 
            | QFact({ p_info = Attacker _ ; _},_,_) -> (i::acc,i+1)
            | _ -> (acc,i+1)
          ) ([],1) prem 
        in

        let rec valid_event = function
          | QFact({ p_info = Attacker _; _},{ ord_target = eord_fun; _},_) ->
            begin match eord_fun with
              | QOSpecific ord_list ->
                  List.iter (function
                    | i,(SemStd,Less) when List.mem i att_idx_prem -> 
                        Parsing_helper.input_error "Attacker facts should not be asked to be proved strictly before an attacker fact of the premise.\nProVerif would never be able to prove such ordering. You should try to show that some process interaction must occur between, e.g. attacker(M)@i ==> event(A)@j && attacker(N)@k && k < j && j < i" ext
                    | _ -> ()
                  ) ord_list
              | _ -> ()
            end
          | _ -> ()
        
        and valid_concl = function
          | QTrue | QFalse | QConstraints _ -> () (* no attacker facts inside constraints *)    
          | NestedQuery(Before(evl,concl)) -> 
              List.iter valid_event evl;
              valid_concl concl
          | QAnd(concl1,concl2)
          | QOr(concl1,concl2) ->
              valid_concl concl1;
              valid_concl concl2
          | QEvent ev -> valid_event ev
        in

        valid_concl concl;
        query'

let exists_at_event = function
  | QSEvent(_,{ temp_var = Some _; _},_,_)
  | QFact(_,{ temp_var = Some _; _},_) -> true
  | (QNeq((t,_),_) | QEq((t,_),_) | QGeq((t,_),_) | QGr((t,_),_)) when Terms.get_term_type t == Param.time_type -> true
  | _ -> false

let rec exists_at_conclusion_query = function
  | QFalse | QTrue | QConstraints _ -> false
  | QEvent ev -> exists_at_event ev
  | NestedQuery rq -> exists_at_realquery rq
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> exists_at_conclusion_query concl1 || exists_at_conclusion_query concl2

and exists_at_realquery = function
  | Before(evl,concl) ->
      List.exists exists_at_event evl || exists_at_conclusion_query concl

(* Treat real-or-random secrecy queries *)

let get_name = function
    FunApp(f,_) -> Terms.get_fsymb_origname f
  | Var v -> v.vname.orig_name

let get_public_vars_encode_step public_vars =
  let pub_vars_and_channels =
    List.map (fun v ->
      let ch_name = "pub_ch_" ^(get_name v) in
      (v,Terms.create_name ~orig:false ch_name ([], Param.channel_type) false)
        ) public_vars
  in
  (Public_vars(pub_vars_and_channels), List.map snd pub_vars_and_channels)

let rec encode_ror_secret_corresp_q next_f pi_state p_desc accu = function
    [] ->
      (* Return the queries that still need to be handled *)
      List.rev accu
  | (QSecret(secrets, public_vars, RealOrRandom),_ as q)::ql ->
      (* Encode the Real-or-Random secrecy query *)
      let encoded_query = ChoiceQEnc(q) in
      let (pub_vars_encode_step, pub_channels) = get_public_vars_encode_step public_vars in
      let pub_channel = Terms.create_name ~orig:false "pub_ch" ([], Param.channel_type) false in
      let encode_steps = [ pub_vars_encode_step;
                           Secret_ror(secrets, pub_channel)]
      in
      let encoded_process = encode_process encode_steps p_desc.proc in
      let encoded_process_desc =
	{ proc = encoded_process;
	  bi_pro = true;
	  display_num = None;
	  construction = Encode(p_desc, encode_steps) }
      in
      let pi_state' =
        { pi_state with
          pi_process_query = SingleProcessSingleQuery(encoded_process_desc, encoded_query);
          pi_freenames = pub_channels @ pub_channel :: pi_state.pi_freenames }
      in
      next_f (Lemma.encode_lemmas pi_state' public_vars (Some secrets));
      (* Handle the other queries *)
      encode_ror_secret_corresp_q next_f pi_state p_desc accu ql
  | q::ql ->
      encode_ror_secret_corresp_q next_f pi_state p_desc (q::accu) ql

let encode_ror_secret1 next_f pi_state p = function
    CorrespQuery(ql,s_status) -> CorrespQuery(encode_ror_secret_corresp_q next_f pi_state p [] ql, s_status)
  | (NonInterfQuery _ | WeakSecret _) as q -> q
  | QueryToTranslate _ ->
      Parsing_helper.internal_error __POS__ "Query should have been translated before encoding"
  | CorrespQEnc _ | ChoiceQEnc _ ->
      Parsing_helper.internal_error __POS__ "Encoded queries should not appear before encoding"
  | ChoiceQuery ->
      Parsing_helper.internal_error __POS__ "Choice query should have been treated before"

let is_put_begin = function
  | PutBegin _,_ -> true
  | _ -> false

let only_put_begin ql =
  List.for_all is_put_begin ql

let rec encode_ror_secret next_f pi_state p accu = function
    [] -> List.rev accu
  | q::ql ->
      let q' = encode_ror_secret1 next_f pi_state p q in
      let accu' =
        match q' with
        | CorrespQuery(ql,_) when only_put_begin ql -> accu
        | _ -> q' :: accu
      in
      encode_ror_secret next_f pi_state p accu' ql

(* Treat other queries: public_vars, secret [reach] *)

let rec find_one_public_vars_corresp = function
    [] -> Parsing_helper.internal_error __POS__ "Empty CorrespQuery (or only putbegin)"
  | (PutBegin _,_)::ql -> find_one_public_vars_corresp ql
  | ((RealQuery(_,public_vars) | QSecret(_,public_vars,_)),_)::_ -> public_vars

let find_one_public_vars = function
    CorrespQuery(ql,_) -> find_one_public_vars_corresp ql
  | NonInterfQuery _ | WeakSecret _ -> []
  | QueryToTranslate _ ->
      Parsing_helper.internal_error __POS__ "Query should have been translated before encoding"
  | CorrespQEnc _ | ChoiceQEnc _ ->
      Parsing_helper.internal_error __POS__ "Encoded queries should not appear before encoding"
  | ChoiceQuery ->
      Parsing_helper.internal_error __POS__ "Choice query should have been treated before"

let includes pv1 pv2 =
  List.for_all (fun v1 -> List.exists (Terms.equal_terms v1) pv2) pv1

let equal_public_vars pv1 pv2 =
  (includes pv1 pv2) && (includes pv2 pv1)

let has_public_vars public_vars = function
    PutBegin _,_ -> false
  | (RealQuery (_,public_vars') | QSecret(_,public_vars',_)),_ ->
      equal_public_vars public_vars public_vars'

let rec partition_public_vars public_vars = function
  | [] -> ([],[])
  | (CorrespQuery(ql,s_status))::rest ->
      let (r1, r2) = partition_public_vars public_vars rest in
      let (ql1, ql2) = List.partition (has_public_vars public_vars) ql in
      (* The previous partition puts the "put_begin" in ql2.
         We want them in both lists, so we add them to ql1 *)
      let ql1 = (List.filter is_put_begin ql) @ ql1 in
      let l1 = if only_put_begin ql1 then r1 else (CorrespQuery (ql1,s_status))::r1 in
      let l2 = if only_put_begin ql2 then r2 else (CorrespQuery (ql2,s_status))::r2 in
      (l1, l2)
  | ((NonInterfQuery _ | WeakSecret _) as q)::rest ->
      let (r1, r2) = partition_public_vars public_vars rest in
      if public_vars == [] then
        (q::r1, r2)
      else
        (r1, q::r2)
  | (QueryToTranslate _)::_ ->
      Parsing_helper.internal_error __POS__ "Query should have been translated before encoding"
  | (CorrespQEnc _ | ChoiceQEnc _)::_ ->
      Parsing_helper.internal_error __POS__ "Encoded queries should not appear before encoding"
  | ChoiceQuery :: _ ->
      Parsing_helper.internal_error __POS__ "Choice query should have been treated before"

let encode_corresp_query ?(id_thread=0) pi_state encode_steps = function
  | (PutBegin _,_) as x -> x
  | (RealQuery(q, public_vars),ext) as x ->
      if public_vars == [] then
        if exists_at_realquery q
        then RealQuery(encode_temporal_realquery_e ~id_thread:id_thread ext q,[]),ext
        else x
      else
        (* Remove the public variables: they are encoded in the process *)
        if exists_at_realquery q
        then RealQuery(encode_temporal_realquery_e ~id_thread:id_thread ext q,[]),ext
        else RealQuery(q, []),ext
  | QSecret(secrets, public_vars, Reachability),ext ->
      let ty = Terms.get_term_type (List.hd secrets) in
      let tyarg = if !Param.key_compromise = 0 then [ty] else [Param.sid_type; ty] in
      let name = (get_name (List.hd secrets)) ^ "_contains" in
      let ev = { f_name = Renamable (Terms.new_id ~orig:false name);
                 f_type = tyarg, Param.event_type;
                 f_cat = Eq[];
                 f_initial_cat = Eq[];
                 f_private = true;
                 f_options = 0;
                 f_record = Param.fresh_record () }
      in
      encode_steps := (Secret_reach(secrets, ev)) :: (!encode_steps);
      let v = Terms.new_var_def_term ty in
      let arg = if !Param.key_compromise = 0 then [v] else [Terms.new_var_def_term Param.sid_type; v] in
      let att_pred = Param.get_pred (Attacker(pi_state.pi_max_used_phase, ty)) in
      (* The query event(x_contains(v)) && attacker(v) ==> false.
         false is encoded as an empty disjunction. *)
      RealQuery(Before([QSEvent(None,{ ord_target = QONone; ord_proved = ref None; temp_var = None },None,FunApp(ev, arg)); QFact(att_pred, { ord_target = QONone; ord_proved = ref None; temp_var = None },[v])], QFalse), []), ext
  | QSecret(_,_,RealOrRandom),_ ->
      Parsing_helper.internal_error __POS__ "secret .. [real_or_random] should have been already encoded"

let encode_reach_secret ?(id_thread=0) pi_state encode_steps = function
  | CorrespQuery(ql,s_status) ->
      let ql' = List.map (encode_corresp_query ~id_thread:id_thread pi_state encode_steps) ql in
      if List.for_all2 (==) ql ql' then
        CorrespQuery(ql,s_status)
      else
        CorrespQEnc((List.combine ql ql'),s_status)
  | x -> x

let rec get_events = function
    [] -> []
  | (Secret_reach(_,e))::r -> e :: (get_events r)
  | _::r -> get_events r

let rec encode_public_vars ?(id_thread=0) next_f pi_state p_desc rest =
  match rest with
    [] -> (* All queries already handled *) ()
  | q::_ ->
      (* find one public_vars *)
      let public_vars = find_one_public_vars q in
      (* separate the queries that have this public_vars from others *)
      let (set1, rest) = partition_public_vars public_vars rest in
      (* encode the queries that have this public_vars *)
      let encode_steps = ref [] in
      let encoded_queries = List.map (encode_reach_secret ~id_thread:id_thread pi_state encode_steps) set1 in
      let new_events = get_events (!encode_steps) in
      let encode_steps', new_free_names =
        if public_vars == [] then
          (!encode_steps), []
        else
          let (pub_vars_encode_step, pub_channels) = get_public_vars_encode_step public_vars in
          pub_vars_encode_step::(!encode_steps), pub_channels
      in
      let encoded_p_desc =
        if encode_steps' == [] then
          p_desc
        else
	  { proc = encode_process encode_steps' p_desc.proc;
	    bi_pro = p_desc.bi_pro;
	    display_num = None;
	    construction = Encode(p_desc, encode_steps') }
      in
      (* Lemmas for queries 'secret x [real_or_random]' should not be taken into account here. *)
      let pi_state1 = Lemma.encode_lemmas pi_state public_vars None in
      next_f { pi_state1 with
          pi_process_query = SingleProcess(encoded_p_desc, encoded_queries);
          pi_freenames = new_free_names @ pi_state1.pi_freenames;
          pi_events = new_events @ pi_state1.pi_events
        };
      (* treat the rest *)
      encode_public_vars ~id_thread:id_thread next_f pi_state p_desc rest

(* Encode lemmas with temporal variables to good one *)

let encode_temporal_lemmas next_f pi_state = 
  let is_equiv = match pi_state.pi_process_query with
    | Equivalence _ | SingleProcessSingleQuery(_, ChoiceQuery) -> true
    | _ -> false
  in

  let new_lemmas = 
    List.fold_left (fun acc -> function
      | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[encode_temporal_lemmas] SHould have been translated already."
      | Lemma lem_state ->
          let lemma_list = 
            List.map (fun lem -> match lem.ql_query with
              | RealQuery(query,[]),ext ->
                  let query' = encode_temporal_realquery_e ext query in
                  let orig = match lem.ql_original_query with
                    | None -> Some lem.ql_query
                    | Some _ -> lem.ql_original_query
                  in
                  let lem' = { lem with ql_query = RealQuery(query',[]),ext; ql_original_query = orig } in
                  Lemma.valid_lemma is_equiv lem';
                  lem'
              | _ -> Parsing_helper.internal_error __POS__ "[encode_temporal_lemmas] All lemmas should be correspondence query without public variables at that point."    
            ) lem_state.lemmas
          in
          (Lemma { lem_state with lemmas = lemma_list }) :: acc
    ) [] pi_state.pi_lemma
  in

  next_f { pi_state with pi_lemma = List.rev new_lemmas }

(* Main encoding functions *)

let encode_aux ?(id_thread=0) next_f pi_state p ql =
  let rest = encode_ror_secret next_f pi_state p [] ql in
  encode_public_vars ~id_thread:id_thread (encode_temporal_lemmas next_f) pi_state p rest

let encode_secret_public_vars ?(id_thread=0) next_f pi_state =
  match pi_state.pi_process_query with
    Equivalence _ | SingleProcessSingleQuery(_, ChoiceQuery) ->
      encode_temporal_lemmas next_f (Lemma.encode_lemmas_for_equivalence_queries pi_state)
  | SingleProcessSingleQuery(p,q) ->
      encode_aux ~id_thread:id_thread next_f pi_state p [q]
  | SingleProcess(p,ql) ->
      encode_aux ~id_thread:id_thread next_f pi_state p ql


let rec get_unlinked_vars_acc_term_e (acc: binder list ref) ((term, _): term_e) = Terms.get_unlinked_vars_acc acc term

let rec get_unlinked_vars_acc_event (acc: binder list ref) (event: event) = 
  match event with
  | QSEvent(_,_,_,t) -> Terms.get_unlinked_vars_acc acc t
  | QSEvent2(_,t1,t2) -> 
      Terms.get_unlinked_vars_acc acc t1;
      Terms.get_unlinked_vars_acc acc t2
  | QFact(_,_, terms) -> List.iter (Terms.get_unlinked_vars_acc acc) terms
  | QNeq(t1, t2) | QEq(t1, t2) | QGeq(t1, t2) | QGr(t1, t2) -> 
      get_unlinked_vars_acc_term_e acc t1;
      get_unlinked_vars_acc_term_e acc t2
  | QIsNat t -> Terms.get_unlinked_vars_acc acc t
  | QMax(t, terms) | QMaxq(t, terms) -> 
      Terms.get_unlinked_vars_acc acc t;
      List.iter (Terms.get_unlinked_vars_acc acc) terms

let rec get_unlinked_vars_acc_conclusion (acc: binder list ref) (conclusion_query: conclusion_query) =
  match conclusion_query with
    QTrue -> ()
  | QFalse -> ()
  | QConstraints q -> Terms.get_unlinked_vars_acc_constra acc q
  | QAnd(c1, c2) -> 
      get_unlinked_vars_acc_conclusion acc c1; 
      get_unlinked_vars_acc_conclusion acc c2
  | QOr(c1, c2) -> 
      get_unlinked_vars_acc_conclusion acc c1; 
      get_unlinked_vars_acc_conclusion acc c2 
  | QEvent e -> get_unlinked_vars_acc_event acc e
  | NestedQuery (Before(hypothesis, conclusion_query)) -> 
      List.iter (get_unlinked_vars_acc_event acc) hypothesis;
      get_unlinked_vars_acc_conclusion acc conclusion_query

let skip_if_term_fails f_next term =
  Terms.auto_cleanup (fun () ->
    try 
      let x = Terms.new_var_def (Terms.get_term_type term) in
      Terms.unify term (Var x);
      f_next ()
    with Terms.Unify -> () 
	)
    
let rewrite_if_destructor_term restwork constr term = 
  (* rewrite if term contains a destructor *)
  if Terms.contains_destructor term
  then
    begin
      (* Choice should have been removed earlier, by Lemma.translate_to_bi_lemma *)
      assert (not (Terms.has_choice term));
      TermsEq.close_term_destr_eq constr (fun constr' term' ->
        skip_if_term_fails (fun _ -> 
            restwork constr' term'
        ) term'
	  ) term
    end
  else
    restwork constr term

let rewrite_if_destructor_term_2 restwork constr (term1: term) (term2: term) =
  rewrite_if_destructor_term (fun constr' term1' ->
    rewrite_if_destructor_term (fun constr'' term2' ->
      restwork constr'' term1' term2'
    ) constr' term2
  ) constr term1

let rec rewrite_destructor_terms restwork accu_constra = function
  | [] -> restwork accu_constra []
  | elt::q ->
      (* rewrite if term contains a destructor *)
      rewrite_if_destructor_term (fun accu_constra1 elt' ->
        rewrite_destructor_terms (fun accu_constra2 q' ->
          restwork accu_constra2 (elt'::q')
        ) accu_constra1 q
      ) accu_constra elt



let rec copy_term_e ((term, extent): term_e): term_e =
  (Terms.copy_term4 term, extent)

let rec copy_event4 (event: event) =
  match event with
    | QSEvent(k, ord, occ, t) -> QSEvent(k, ord, occ, Terms.copy_term4 t)
    | QSEvent2(ord,t1,t2) -> QSEvent2(ord, Terms.copy_term4 t1, Terms.copy_term4 t2)
    | QFact(pred, ord, terms) -> QFact(pred, ord, List.map Terms.copy_term4 terms)
    | QNeq(t1, t2) -> QNeq(copy_term_e t1, copy_term_e t2)
    | QEq(t1, t2) -> QEq(copy_term_e t1, copy_term_e t2)
    | QGeq(t1, t2) -> QGeq(copy_term_e t1, copy_term_e t2)
    | QGr(t1, t2) -> QGr(copy_term_e t1, copy_term_e t2)
    | QIsNat t -> QIsNat(Terms.copy_term4 t)
    | QMax(t, terms) -> QMax(t, List.map Terms.copy_term4 terms)
    | QMaxq(t, terms) -> QMaxq(t, List.map Terms.copy_term4 terms)
      
let rec copy_conclusion_query4 (conclusion_query: conclusion_query) =
  match conclusion_query with
    QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints q -> QConstraints(Terms.copy_constra4 q)
  | QAnd(c1, c2) -> QAnd(copy_conclusion_query4 c1, copy_conclusion_query4 c2)
  | QOr(c1, c2) -> QOr(copy_conclusion_query4 c1, copy_conclusion_query4 c2)
  | QEvent e -> QEvent(copy_event4 e)
  | NestedQuery rq -> NestedQuery(copy_real_query4 rq)

and copy_real_query4 (realquery: realquery) =
  match realquery with
    | Before(hypothesis, conclusion_query) -> 
      (* destructors can only occur in conclusions, hence do not need to copy in hypothesis *)
      Before(hypothesis, copy_conclusion_query4 conclusion_query)

let rec encode_destructors_in_event f_next cons (event: event) =
  match event with
  | QSEvent(k, ord, occ, t) -> rewrite_if_destructor_term (fun cons' t' -> 
      f_next cons' (QSEvent(k, ord, occ, t'))
    ) cons t
  | QSEvent2(ord, t1, t2) -> rewrite_if_destructor_term_2 (fun cons' t1' t2' -> 
      f_next cons' (QSEvent2(ord, t1', t2'))
  ) cons t1 t2
  | QFact(pred, ord, terms) -> rewrite_destructor_terms (fun cons' terms' ->
      f_next cons' (QFact(pred, ord, terms'))
    ) cons terms
  | QIsNat(t) -> rewrite_if_destructor_term (fun cons' t' -> 
      f_next cons' (QIsNat(t'))
    ) cons t
  | QNeq((t1, e1), (t2, e2)) -> rewrite_if_destructor_term_2 (fun cons' t1' t2' ->
      f_next cons' (QNeq((t1', e1), (t2', e2)))
    ) cons t1 t2
  | QEq((t1, e1), (t2, e2)) -> rewrite_if_destructor_term_2 (fun cons' t1' t2' ->
      f_next cons' (QEq((t1', e1), (t2', e2)))
    ) cons t1 t2
  | QGeq((t1, e1), (t2, e2)) -> rewrite_if_destructor_term_2 (fun cons' t1' t2' ->
      f_next cons' (QGeq((t1', e1), (t2', e2)))
    ) cons t1 t2  
  | QGr((t1, e1), (t2, e2)) -> rewrite_if_destructor_term_2 (fun cons' t1' t2' ->
      f_next cons' (QGr((t1', e1), (t2', e2)))
    ) cons t1 t2
  | (QMax _ | QMaxq _) as q -> f_next cons q (* it is checked in exists_destructor_in_event that in these other cases here, there cannot occur a destructor *)
  
let rec encode_destructed_in_conclusion_query ?(id_thread=0) (sub_cl: conclusion_query) cl_acc = 
  let vars_sub_cl = 
    let acc = ref [] in
    get_unlinked_vars_acc_conclusion acc sub_cl;
    !acc
  in
  encode_destructors_in_conclusion_query ~id_thread:id_thread (fun cons' sub_cl' ->
    let sub_cl_acc = ref (copy_conclusion_query4 sub_cl') in
    List.iter (fun v -> match (v.link).(id_thread) with
      | NoLink -> ()
      | TLink t -> 
          let t' = Terms.copy_term4 t in
          let v_ext = (Var v, Parsing_helper.dummy_ext) in
          let t_ext = (t',Parsing_helper.dummy_ext) in
          sub_cl_acc := Reduction_helper.make_qand (QEvent(QEq(v_ext,t_ext))) !sub_cl_acc
      | _ -> Parsing_helper.internal_error __POS__ ("Unexpected link type")
    ) vars_sub_cl;
    sub_cl_acc := Reduction_helper.make_qand (QConstraints (Terms.copy_constra4 cons')) !sub_cl_acc;
    cl_acc := Reduction_helper.make_qor !cl_acc !sub_cl_acc
  ) Terms.true_constraints sub_cl
    
and encode_destructors_in_conclusion_query ?(id_thread=0) f_next cons = function
  | QTrue -> f_next cons QTrue
  | QFalse -> f_next cons QFalse
  | QConstraints _ as q -> f_next cons q
	(* QConstraints never contain destructors, because they are only
	   generated in this encoding of destructors *)
  | QEvent ev ->
      encode_destructors_in_event (fun cons' ev' -> 
          f_next cons' (QEvent ev')
      ) cons ev
  | QAnd(cl1,cl2) ->
      encode_destructors_in_conclusion_query ~id_thread:id_thread (fun cons1 cl1' ->
        encode_destructors_in_conclusion_query ~id_thread:id_thread (fun cons2 cl2' ->
          f_next cons2 (Reduction_helper.make_qand cl1' cl2')
        ) cons1 cl2
      ) cons cl1
  | QOr(cl1,cl2) ->
      let cl_acc = ref QFalse in

      encode_destructed_in_conclusion_query ~id_thread:id_thread cl1 cl_acc;
      encode_destructed_in_conclusion_query ~id_thread:id_thread cl2 cl_acc;

      f_next cons !cl_acc
  | NestedQuery nq -> 
      let nq' = encode_destructors_in_realquery ~id_thread:id_thread nq in
      f_next cons (NestedQuery nq')

and encode_destructors_in_realquery ?(id_thread=0) (Before(hypothesis, conclusion_query)) =
  (* Destructuring the hypothesis is not yet supported. Supporting this would need to introduce a structure to support multiple encoded queries for a single source query. 
     See also [exists_destructor_in_realquery] and [copy_real_query4] which use this assumption. *)
  let cl_acc = ref QFalse in
  encode_destructed_in_conclusion_query ~id_thread:id_thread conclusion_query cl_acc;
  Before(hypothesis, !cl_acc)

let rec exists_destructor_in_event (event: event) =
  match event with
  | QSEvent(_,_,_, t) -> Terms.contains_destructor t
  | QSEvent2(ord, t1, t2) -> Terms.contains_destructor t1 || Terms.contains_destructor t2
  | QFact(pred, ord, terms) -> List.exists Terms.contains_destructor terms
  | QNeq((t1, e1), (t2, e2))| QEq((t1, e1), (t2, e2)) | QGeq((t1, e1), (t2, e2)) | QGr((t1, e1), (t2, e2)) -> Terms.contains_destructor t1 || Terms.contains_destructor t2
  | QIsNat(t) -> Terms.contains_destructor t
  | QMax(t, tl) | QMaxq(t, tl) -> 
    if Terms.contains_destructor t || List.exists Terms.contains_destructor tl
      then
        Parsing_helper.internal_error __POS__ "Destructors are not supported in max and maxq"
      else
        false

let rec exists_destructor_in_conclusion_query = function
  | QTrue | QFalse | QConstraints _ -> false
	(* QConstraints never contain destructors, because they are only
	   generated in this encoding of destructors *)
  | QEvent ev -> exists_destructor_in_event ev
  | QAnd(cl1,cl2)
  | QOr(cl1,cl2) -> exists_destructor_in_conclusion_query cl1 || exists_destructor_in_conclusion_query cl2
  | NestedQuery rq -> exists_destructor_in_realquery rq
      
and exists_destructor_in_realquery (Before(hypothesis, conclusion_query)) =
  (* destructors can only occur in conclusions *)
  exists_destructor_in_conclusion_query conclusion_query
  
let exists_destructor_in_query_e = function
  | (RealQuery(real_query, term_list), extent) ->
      exists_destructor_in_realquery real_query
  | _ -> false
  
let encode_destructors_in_query_e ?(id_thread=0) = function
  | (RealQuery(real_query, term_list), extent) -> 
      (RealQuery(encode_destructors_in_realquery ~id_thread:id_thread real_query, term_list), extent)
  | _ as q -> q

let encode_destructors_in_t_lemmas ?(id_thread=0) (lemma: t_lemmas) =
  match lemma with
  | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[encode_destructors_in_t_lemmas] Should have been translated already."
  | Lemma lem_state -> 
    let new_lemmas = List.map (fun lemma -> 
      let new_query = encode_destructors_in_query_e ~id_thread:id_thread lemma.ql_query in
      { lemma with ql_query = new_query }
      ) lem_state.lemmas 
    in
    Lemma { lem_state with lemmas = new_lemmas }


let encode_destructors_in_t_query ?(id_thread=0) = function
    CorrespQuery(ql,s_status) as qc -> 
      if List.exists exists_destructor_in_query_e ql
        then
          CorrespQEnc (List.map (fun original -> (original, encode_destructors_in_query_e ~id_thread:id_thread original)) ql, s_status)
        else 
          qc
  | CorrespQEnc(query_list,s_status) -> 
      CorrespQEnc (List.map (fun (original, encoded) -> (original, encode_destructors_in_query_e ~id_thread:id_thread encoded)) query_list, s_status)
  | ChoiceQEnc _ |  ChoiceQuery | NonInterfQuery _ | WeakSecret _ as q -> q 
  | QueryToTranslate _ ->
      Parsing_helper.internal_error __POS__ "Query should have been translated before encoding"

let encode_destructors_process ?(id_thread=0) = function
    (Equivalence _) as p -> p
  | SingleProcessSingleQuery(p,q) ->
    let new_query = encode_destructors_in_t_query ~id_thread:id_thread q in
    SingleProcessSingleQuery(p, new_query)
  | SingleProcess(p,ql) ->
    let new_queries = List.map (encode_destructors_in_t_query ~id_thread:id_thread) ql in
    SingleProcess(p, new_queries)

let encode_destructors ?(id_thread=0) pi_state =
  let new_process_query = encode_destructors_process ~id_thread:id_thread pi_state.pi_process_query in
  let new_axioms =
    List.map (fun ((query, extent), b) ->
      ((encode_destructors_in_realquery ~id_thread:id_thread query, extent), b)
	) pi_state.pi_original_axioms
  in
  let new_lemmas = List.map (encode_destructors_in_t_lemmas ~id_thread:id_thread) pi_state.pi_lemma in
  { pi_state with pi_process_query = new_process_query; pi_original_axioms = new_axioms; pi_lemma = new_lemmas }

(* Give the fact to query from the detailed query
   This is used only to create a resembling specification for SPASS
 *)

let query_to_facts pi_state =
  let facts = ref [] in
  let q_to_facts = function
      PutBegin _,_ -> ()
    | RealQuery(Before(el,_), []),_ ->
        List.iter (function
            QSEvent(_,_,_,(FunApp(f,l) as param)) ->
              facts :=
                 (if (Pievent.get_event_status pi_state f).end_status = WithOcc then
                   Pred(Param.inj_event_pred, [param;Var(Terms.new_var ~orig:false "endsid" Param.sid_type)])
                 else
                   Pred(Param.event_pred, [param])) :: (!facts)
          | QSEvent _ ->
              Parsing_helper.user_error "Events should be function applications"
          | QSEvent2 _ -> Parsing_helper.user_error "Unexpected event"
          | QFact(p,_,l) ->
              facts := (Pred(p,l)) :: (!facts)
          | QNeq _ | QEq _ | QGeq _ | QIsNat _ | QGr _ -> Parsing_helper.internal_error __POS__ "no Neq/Eq/IsNat/Geq queries"
          | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "no Max and Maxq in queries"
                ) el
    | (QSecret _ | RealQuery _),_ ->
        Parsing_helper.internal_error __POS__ "Query secret and queries with public variables should have been encoded before query_to_facts"
  in
  let q2_to_facts = function
      CorrespQuery(ql,_) -> List.iter q_to_facts ql
    | CorrespQEnc(qql,_) -> List.iter (fun (_,q) -> q_to_facts q) qql
    | _ ->
        Parsing_helper.internal_error __POS__ "query_to_facts applies only to correspondence queries"
  in
  begin
    match pi_state.pi_process_query with
    | Equivalence _ ->
        Parsing_helper.internal_error __POS__ "query_to_facts does not apply to equivalence queries"
    | SingleProcess(_, ql) -> List.iter q2_to_facts ql
    | SingleProcessSingleQuery(_,q) -> q2_to_facts q
  end;
  !facts
