open Parsing_helper
open Types
open Pitypes
open Terms
open Clause
open Utils

let supplemental_info = ref []

let declared_axioms = ref []

let faulty_clauses_injective = ref []

let success_clauses = ref []

let for_biprocess = ref false

let traces_to_reconstruct = ref 0
let shown_stop = ref false

(* Display a clause and possibly a corresponding trace
   When inj_mode = Some q, try to reconstruct a trace that falsifies injectivity
   When inj_mode = None, just try to reconstruct a trace corresponding
   to the derivation of the clause cl.
   Returns true when a trace has definitely been found.
 *)

let display_clause_trace id_thread lemmas detail recheck opt_query list_started cl =
  Display.Text.print_string "goal reachable: ";
  Ord.Text.display_abbrev cl;
  if !Param.html_output then
    begin
      if not (!list_started) then
        begin
          list_started := true;
          Display.Html.print_string "<UL>\n";
        end;
      Display.Html.print_string "<LI>goal reachable: ";
      Ord.Html.display_abbrev cl
    end;

  (* This will need to be removed before release *)
  let no_liveness () = 
    if !Param.current_state.pi_requires_liveness
    then 
      begin 
        Display.Text.print_line "Warning: Trace reconstruction with liveness is currently not implemented";
        false
      end
    else true
  in

  (* TulaFale expects a derivation after "goal reachable" *)
  if (detail || (!Param.tulafale = 1)) && no_liveness () then
    begin
      try
        let verify_rule clause = 
          Display.auto_cleanup_display (fun () ->
            auto_cleanup (fun () ->
              let deriv = History.build_history recheck clause in
              if (!traces_to_reconstruct != 0) && (!Param.reconstruct_derivation) &&
                (!Param.key_compromise == 0) 
              then 
                begin 
                  History.unify_derivation (fun new_tree ->
                    if !traces_to_reconstruct > 0 then decr traces_to_reconstruct;
                    if !for_biprocess
                    then Reduction_bipro.do_reduction opt_query !declared_axioms new_tree
                    else Reduction.do_reduction opt_query !declared_axioms new_tree
                  ) recheck deriv
                end
              else false
            )
          )
        in

        let first_result = verify_rule cl in

        if ((!traces_to_reconstruct != 0) && (!Param.reconstruct_derivation) &&
          (!Param.key_compromise == 0)) && (not first_result)
        then 
          begin 
            let second_result = 
              
              if (cl.Ord.constraints.is_nat <> [] || cl.Ord.constraints.geq <> []) && (!traces_to_reconstruct != 0)
              then
                try
                  TermsEq.get_solution (fun () ->
                    let cl' = Ord.copy2 cl in
                    Terms.auto_cleanup (fun () ->
                      (* When we try to find the attack trace, we only apply the lemmas but not the inductive lemmas. *)
                      let clauses = Rules.solving_request_rule lemmas cl' in
                      
                      if clauses = []
                      then false
                      else
                        begin
                          Display.Text.newline ();
                          Display.Text.print_line "Presence of natural number in the clause. We try to resolve more the clause to obtain an attack trace.";
                          if !Param.html_output
                          then Display.Html.print_line "Presence of natural number in the clause. We try to resolve more the clause to obtain an attack trace.";
                          Parsing_helper.debug (fun () ->
                            let check_one_term = 
                              Terms.iter_variables (fun v ->
                                if v.link.(id_thread) <> NoLink then assert(false)
                              )
                            in
                            List.iter (Ord.iter_term check_one_term) clauses
                          );
                          List.exists (fun cl ->
                            if !traces_to_reconstruct != 0 
                            then verify_rule cl
                            else false
                          ) clauses
                        end
                    )
                  ) cl.Ord.constraints
                with TermsEq.FalseConstraint -> false
              else false
            in
            if (not second_result) && (!traces_to_reconstruct = 0) && (!Param.reconstruct_trace > 0) && (not !shown_stop) then
              begin
                shown_stop := true;
                Display.Def.print_line "Stopping attack reconstruction attempts. To try more traces, modify the setting reconstructTrace.";
              end;
            second_result
          end
        else first_result
      with Not_found ->
        (* When the derivation could not be reconstructed *)
        cleanup ();
        false
    end
  else
    false

(* Link variables of a fact to new constants, of type "SpecVar" *)

let put_constants_rule (hyp, concl, hist, constra) =
  List.iter (fun (f,_) -> put_constants_fact f) hyp;
  put_constants_fact concl;
  Terms.iter_constraints put_constants constra

(* Copy a query, following links inside variables *)

let copy_query = TermsEq.copy_remove_syntactic_realquery

(* Transforms a query into a non-injective, non-nested one

   The function [Piauth.simplify_query] must provide a stronger query
   than the simplified queries produced using
   [Lemma.simplify_induction_conclusion_query], because the proof of
   the query obtained by [Piauth.simplify_query] allows us to apply
   the inductive lemma.
   In particular, we simplify nested queries [e ==> concl] into conjunctions
   [e && concl] in both functions. *)

let non_inj_event = function
    QSEvent(_,ord_fun,occ,t) -> QSEvent(None,ord_fun,occ,t)
  | e -> e

let rec simplify_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints _ as q -> q (* no transformation, as no nesting/injectivity inside possible *)
  | QEvent e -> QEvent(non_inj_event e)
  | NestedQuery(Before([e],concl)) ->
      QAnd(QEvent(non_inj_event e), simplify_conclusion_query concl)
  | NestedQuery _ ->
      Parsing_helper.internal_error __POS__ "[simplify_conclusion_query] Nested queries should have exactly one premise."
  | QAnd(concl1,concl2) ->
      QAnd(simplify_conclusion_query concl1, simplify_conclusion_query concl2)
  | QOr(concl1,concl2) ->
      QOr(simplify_conclusion_query concl1, simplify_conclusion_query concl2)

let simplify_query (Before(el,concl)) =
  Before(List.map non_inj_event el, simplify_conclusion_query concl)

let rec remove_nested_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints q -> QConstraints q
  | QEvent e -> QEvent e
  | NestedQuery(Before([e],_)) -> QEvent e
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[remove_nested_conclusion_query] Nested queries should have exactly one premise."
  | QAnd(concl1,concl2) -> QAnd(remove_nested_conclusion_query concl1,remove_nested_conclusion_query concl2)
  | QOr(concl1,concl2) -> QOr(remove_nested_conclusion_query concl1, remove_nested_conclusion_query concl2)

let remove_nested (Before(el,concl)) =
  Before(el,remove_nested_conclusion_query concl)

let rec is_non_nested_conclusion_query = function
  | QTrue
  | QFalse
  | QConstraints _
  | QEvent _ -> true
  | QAnd(q1,q2) | QOr(q1,q2) -> is_non_nested_conclusion_query q1 && is_non_nested_conclusion_query q2
  | NestedQuery _ -> false

let is_non_nested_query = function
  | Before(_,concl) -> is_non_nested_conclusion_query concl

let is_non_injective_event = function
    QSEvent(Some _,_,_,_) -> false
  | _ -> true

let rec is_non_injective_conclusion_query = function
  | QTrue
  | QFalse 
  | QConstraints _ -> true
  | QEvent e -> is_non_injective_event e
  | NestedQuery q -> is_non_injective_query q
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> is_non_injective_conclusion_query concl1 && is_non_injective_conclusion_query concl2

and is_non_injective_query = function
  | Before(el,concl) ->
      List.for_all is_non_injective_event el && is_non_injective_conclusion_query concl

let is_simple_query q = is_non_nested_query q && is_non_injective_query q

(* Removal of clause subsumed by each other modulo the equational theory. *)

let rec remove_subsumed_mod_eq = function
    [] -> []
  | (a::l) ->
      if List.exists (fun r1 -> Database.SubOrdClause.implies_mod_eq_set r1 a) l then
        remove_subsumed_mod_eq l
      else
        a::(remove_subsumed_mod_eq (List.filter (fun r2 -> not (Database.SubOrdClause.implies_mod_eq_set a r2)) l))

(* Improved verification of predicates in clauses *)

let init_clauses = ref []

let clauses_for_preds_Std = ref None
let clauses_for_preds_Phaseless = ref None

let get_clauses_for_preds_Phaseless () =
  match !clauses_for_preds_Phaseless with
    | Some l -> l
    | None ->
        let clauses = ref [] in

        List.iter (fun (hyp1, concl1, constra1, tag1) ->
          TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
            clauses := (hyp, concl, Rule(-1, tag1, hyp, concl, constra), constra) :: (!clauses)
          ) (hyp1, concl1, constra1)
        ) (!Param.current_state).pi_input_clauses;

        List.iter (fun fact ->
          TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
            clauses := (hyp, concl, Rule(-1, LblClause, hyp, concl, constra), constra) :: (!clauses)
          ) ([], fact, Terms.true_constraints)
        ) (!Param.current_state).pi_elimtrue;

        Terms.cleanup();

        List.iter (function
          | (_,_,Rule(_,(Apply _ | Init ), _,_,_), _) as cl -> clauses := cl :: (!clauses)
          | _ -> ()
        ) (!init_clauses);

        clauses_for_preds_Phaseless := Some (!clauses);
        !clauses

let get_clauses_for_preds_Std () =
  match !clauses_for_preds_Std with
    | Some l -> l
    | None ->
        let clauses = ref (get_clauses_for_preds_Phaseless ()) in
        List.iter (function
          | (_,_,Rule(_,(PhaseChange | TblPhaseChange), _,_,_), _) as cl -> clauses := cl :: (!clauses)
          | _ -> ()
        ) (!init_clauses);
        clauses_for_preds_Std := Some (!clauses);
        !clauses

(* Generation of request rules *)

let rec split_event_constra = function 
  | [] -> [], Terms.true_constraints
  | QNeq ((t1,_),(t2,_)) :: q_evl -> 
      let constra = Terms.constraints_of_neq t1 t2 in
      let evl', constra' = split_event_constra q_evl in
      evl', Terms.wedge_constraints constra constra'
  | QGeq ((t1,_),(t2,_)) :: q_evl -> 
      let constra = Terms.constraints_of_geq t1 t2 in
      let evl', constra' = split_event_constra q_evl in
      evl', Terms.wedge_constraints constra constra'
  | QIsNat t :: q_evl -> 
      let constra = Terms.constraints_of_is_nat t in
      let evl', constra' = split_event_constra q_evl in
      evl', Terms.wedge_constraints constra constra'
  | ev :: q_evl ->
        let evl', constra' = split_event_constra q_evl in
        ev::evl', constra'

let event_to_end_fact = function
  | QSEvent(_,_,None,(FunApp(f,l) as param)) ->
      if (Pievent.get_event_status (!Param.current_state) f).end_status = WithOcc
      then
        let v = Var(Terms.new_var ~orig:false "endocc" Param.occurrence_type) in
        Pred(Param.inj_event_pred, [param;v])
      else
        Pred(Param.event_pred, [param])
  | QSEvent(_,_,Some occ,(FunApp(f,l) as param)) ->
      assert ((Pievent.get_event_status (!Param.current_state) f).end_status = WithOcc);
      Pred(Param.inj_event_pred,[param;occ])
  | QSEvent _ -> user_error ("Events should be function applications")
  | QSEvent2(_,t1,t2) -> Pred(Param.event2_pred,[t1;t2])
  | QFact(p,ord_fun,l) -> Pred(p,l)
  | QNeq _ | QEq _ | QGeq _ | QIsNat _ | QGr _-> internal_error __POS__ "no Neq, Eq, Geq, Ge, IsNat queries"
  | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "[event_to_end_fact] Queries with max inequalities should not occur."

let event_list_to_rule (nb_std,nb_user) evl = 
  let evl_no_constra, constra = split_event_constra evl in
  match evl_no_constra with
  | [e] ->
      let g = event_to_end_fact e in
      
      ([g], g, Rule(-1, Goal, [g], g, constra), constra)
  | el ->
      let hyp = List.map event_to_end_fact el in
      let pl = List.map (function Pred(p,_) -> p) hyp
      in
      let combined_pred = Param.get_pred (Combined(nb_std,nb_user,pl)) in
      let args = List.concat (List.map (function Pred(_,l) -> l) hyp)
      in
      let concl = Pred(combined_pred, args) in
      (hyp, concl, Rule(-1, GoalCombined, hyp, concl, constra), constra)

let generate_initial_request_rule (Before(el,_) as rq) =
  let (nb_std,nb_user) = Query.count_std_and_user_facts rq in
  let (hypl,concl,hist,constra) = event_list_to_rule (nb_std,nb_user) el in
  let hypl' = List.mapi (fun i f -> HypOrd.create_hypothesis_from_nth_conclusion (i+1) f) hypl in

  {
    Ord.hypotheses = hypl';
    Ord.conclusion = concl;
    Ord.history = hist;
    Ord.constraints = constra
  }

(* Generation of occurrence and hypothesis from the conclusion *)

module IntComp =
  struct
    type t = int
    let compare = compare
  end

module IntMap = Tree.MakeOne(IntComp)

type injective_data =
  {
    list_predicates : predicate list;
    arguments : term list;
    occurrences : term list
  }

(* An index of the collector corresponds to the occurrence of an event [evq] in the query.
  To each index is associated a list of tuples (ev,clause,occ_concl) where:
  - [ev] is the event of the hypothesis of [clause] matching [evq]
  - [clause] is the clause being checked (typically obtain by [resolve_hyp])
  - [occ_concl] are the occurrences of events in the conclusion of [clause] that are
    matched with injective events from the premise of the query.
*)
let current_inj_collector = ref (IntMap.empty : ((int * fact) * Ord.clause * term list * injective_data) list IntMap.t)

let add_in_inj_collector clause occ_concl occ_list inj_data =
  List.iter (fun (i,ev) ->
    current_inj_collector :=
    IntMap.update i (function
      | None -> Some [ev,clause,occ_concl,inj_data]
      | Some l -> Some ((ev,clause,occ_concl,inj_data)::l)
    ) !current_inj_collector
  ) occ_list

let rec occurrence_of_conclusion_predicate_rec initial_nb_premise n evl args = match evl with
  | [] ->
      if args = []
      then [],[]
      else Parsing_helper.internal_error __POS__ "[occurrence_of_conclusion_predicate_rec] Conclusion does not match the query."
  | QSEvent(inj,_,_,(FunApp(f,_)))::evl' ->
      begin match (Pievent.get_event_status (!Param.current_state) f).end_status, args with
        | WithOcc, ev::occ::args_q ->
            (* In such a case, the end predicate is injective *)
            let (hypl,occ_concl) = occurrence_of_conclusion_predicate_rec initial_nb_premise (n-1) evl' args_q in
            let hypl' = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
              | No -> hypl
              | NoOcc -> (n,HypOrd.create_hypothesis_from_nth_conclusion (-n) (Pred(Param.event_pred_block,[ev]))) :: hypl
              | WithOcc -> (n,HypOrd.create_hypothesis_from_nth_conclusion (-n) (Pred(Param.inj_event_pred_block,[ev; occ]))) :: hypl
            in
            if inj = None || (-n) > initial_nb_premise
            then (hypl',occ_concl)
            else (hypl',occ::occ_concl)
        | NoOcc, ev::args_q ->
            (* In such a case, the end predicate is non injective.
               Moreover, the begin status can only be No or NoOcc. *)
            let (hypl,occ_concl) = occurrence_of_conclusion_predicate_rec initial_nb_premise (n-1) evl' args_q in
            let hypl' = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
              | No -> hypl
              | NoOcc -> (n,HypOrd.create_hypothesis_from_nth_conclusion (-n) (Pred(Param.event_pred_block,[ev]))) :: hypl
              | _ -> Parsing_helper.internal_error __POS__ "[occurrence_of_conclusion_predicate_rec] Cannot be WithOcc status."
            in
            (hypl',occ_concl)
        | _ -> Parsing_helper.internal_error __POS__ "[occurrence_of_conclusion_predicate_rec] The predicate cannot have a No end_status while being in the premise of the query."
      end
  | QSEvent2(_,t1,t2)::evl' ->
      let args_p', rest_args = List.split_nth 2 args in
      let (hypl,occ_concl) = occurrence_of_conclusion_predicate_rec initial_nb_premise (n-1) evl' rest_args in
      ((n,HypOrd.create_hypothesis_from_nth_conclusion (-n) (Pred(Param.event2_pred_block,[t1;t2])))::hypl,occ_concl)
  | QFact(p,_,args_p)::evl' ->
      let nb_args = List.length args_p in
      let args_p', rest_args = List.split_nth nb_args args in
      let fact = Pred(p,args_p') in
      let (hypl,occ_concl) = occurrence_of_conclusion_predicate_rec initial_nb_premise (n-1) evl' rest_args in
      ((n,HypOrd.create_hypothesis_from_nth_conclusion (-n) fact)::hypl,occ_concl)
  | _ -> internal_error __POS__ "[occurrence_of_conclusion_predicate_rec] Unexpected case."

(* [occurrence_and_hyp_of_conclusion_predicate evl pred] returns a pair of list [hyp_ev], [occ_concl] where
    - [hyp_ev] are the non-injective events and predicates from the conclusion that will be added in the hypotheses of the clause.
    - [occ_concl] are the occurrences of events in the conclusion of [clause] that are
      matched with injective events from the premise of the query.
   When we want to prove a trivial query such as event(A) ==> event(A), the clause generated by proverif does not
   contain begin(A) -> end(A) but only -> end(A). This is why we need to add begin(A) to the hypotheses of clause.
   This is however not the case when events are injective (hence the distinction in [occurrence_of_conclusion_predicate_rec]).

   [occ_concl] corresponds to the function occ_n(C)\sigma from the technical report where
     - n = initial_nb_premise
     - \sigma is the substitution of the solution.
*)
let occurrence_and_hyp_of_conclusion_predicate initial_nb_premise evl = function
  | Pred({ p_info = Combined _; _}, args) ->
      occurrence_of_conclusion_predicate_rec initial_nb_premise (-1) evl args
  | Pred(p,[FunApp(f,_) as ev;occ]) when p == Param.inj_event_pred ->
      assert(initial_nb_premise = 1);
      let hypl = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
        | No -> []
        | NoOcc -> [-1,HypOrd.create_hypothesis_from_nth_conclusion 1 (Pred(Param.event_pred_block,[ev]))]
        | WithOcc -> [-1,HypOrd.create_hypothesis_from_nth_conclusion 1 (Pred(Param.inj_event_pred_block,[ev; occ]))]
      in
      let occ_concl =  match evl with
        | [QSEvent(None,_,_,(FunApp(_,_)))] -> []
        | _ -> [occ]
      in
      hypl,occ_concl
  | Pred(p,[FunApp(f,_) as ev]) when p == Param.event_pred ->
      assert(initial_nb_premise = 1);
      let hypl = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
        | No -> []
        | _ -> [-1,HypOrd.create_hypothesis_from_nth_conclusion 1 (Pred(Param.event_pred_block,[ev]))]
      in
      hypl,[]
  | Pred(p,[FunApp(f,_) as ev1;ev2]) when p == Param.event2_pred ->
      assert(initial_nb_premise = 1);
      let hypl = match (Pievent.get_event_status (!Param.current_state) f).begin_status with
        | No -> []
        | _ -> [-1,HypOrd.create_hypothesis_from_nth_conclusion 1 (Pred(Param.event2_pred_block,[ev1;ev2]))]
      in
      hypl,[]
  | ev ->
      assert(initial_nb_premise = 1);
      [-1,HypOrd.create_hypothesis_from_nth_conclusion 1 ev],[]

exception InjectivityUnverifiable

let get_sid n args =
  let rec get_sid_rec args pim = match args, pim with
    | [],[] -> None
    | [], _ | _, [] -> Parsing_helper.internal_error __POS__ "[get_sid] Unexpected argument."
    | sid::_,(MSid _)::_ -> Some sid
    | _::pi_q, _::pim_q -> get_sid_rec pi_q pim_q
  in
  get_sid_rec args n.prev_inputs_meaning

let generate_constra_occ constra_l occ_concl1 occ_concl2 =
  try
    let constra_neq_disj =
      List.fold_left2 (fun acc occ1 occ2 -> match occ1, occ2 with
        | FunApp({ f_cat = Name n1; _} as f1,args1), FunApp( {f_cat = Name n2; _} as f2,args2) ->
            if f1 == f2
            then
              match get_sid n1 args1, get_sid n2 args2 with
                | None, None -> acc
                | Some sid1, Some sid2 -> (sid1,sid2) :: acc
                | _ -> Parsing_helper.internal_error __POS__ "[generate_constra_occ] Should always have the same sid pattern"
            else raise Unify
        | _ -> Parsing_helper.internal_error __POS__ "[generate_constra_occ] Should always be names."
      ) [] occ_concl1 occ_concl2
    in
    if constra_neq_disj = []
    then raise TermsEq.FalseConstraint
    else { constra_l with neq = constra_neq_disj::constra_l.neq }
  with
    | TermsEq.FalseConstraint -> raise Unify
    | Unify -> constra_l

let generate_injective_data evl =
  let is_inj = ref false in

  let l_pred_occ =
    List.map (function
      | QSEvent(inj,_,_,FunApp(f,_)) ->
          let need_occ =
            if inj = None
            then false
            else (is_inj := true; true)
          in
          if (Pievent.get_event_status (!Param.current_state) f).end_status = WithOcc
          then Param.inj_event_pred, need_occ
          else Param.event_pred, need_occ
      | QSEvent2 _ -> Param.event2_pred, false
      | QFact(p,_,_) -> p,false
      | _ -> internal_error __POS__ "[generate_injective_data] Unexpected case."
    ) evl
  in

  if !is_inj
  then
    let l_pred = List.map (fun (p,_) -> p) l_pred_occ in
    let (args,occs) =
      List.fold_right (fun (p,b) (acc_args,acc_occ) ->
        if p == Param.inj_event_pred
        then
          let x_occ = Var(Terms.new_var ~orig:false "endocc" Param.occurrence_type) in
          let x_ev = Terms.new_var_def_term Param.event_type in
          if b
          then (x_ev::x_occ::acc_args, x_occ::acc_occ)
          else (x_ev::x_occ::acc_args, acc_occ)
        else
          ((List.fold_right (fun t acc -> (Terms.new_var_def_term t)::acc) p.p_type acc_args),acc_occ)
      ) l_pred_occ ([],[])
    in
    Some { list_predicates = l_pred; arguments = args; occurrences = occs }
  else None
 
let copy_injective_data inj_data =
  Terms.auto_cleanup (fun () ->
    { inj_data with
      arguments = List.map Terms.copy_term inj_data.arguments;
      occurrences = List.map Terms.copy_term inj_data.occurrences }
  )

(* [compare_two_clauses ((n1,ev1),cl1,occ_concl1,injdata1) ((n2,ev2),cl2,occ_concl2,injdata2)] checks that the two clauses
  satisfies injectivity with respect to an injective event [ev] in the conclusion of the query.
    - [ni] is the position of [evi] in the hypotheses [cli] matching [ev].
    - [occ_concli] are the occurrences of events in the conclusion of [cli] that are matched with injective events from the premise of the query
    - [inj_datai] is the injectivity information generated by [generate_injective_data].
  The function generate a clause combining [rule1] and [rule2] that unifies [ev1] and [ev2] and adds the disequality [occ_concl1 <> occ_concl2].
  If the hypotheses of the resulting clause do not yield a contradiction by normalisation, then the injectivity cannot be proved.
*)
let compare_two_clauses lemmas ((n1,ev1),cl1,occ_concl1,inj_data1) ((n2,ev2),cl2,occ_concl2,inj_data2) =
  try
    let injective_clause =
      Terms.auto_cleanup (fun () ->
        Terms.unify_facts ev1 ev2;
        let inj_data1 = copy_injective_data inj_data1 in
        let inj_data2 = copy_injective_data inj_data2 in
        let pred_combined = Param.get_pred (Combined(0,0,inj_data1.list_predicates @ inj_data2.list_predicates)) in
	   (* The first 2 arguments of Combined are normally the number of standard and
	      user-defined predicates in the initial query. They are used for proofs by induction.
	      Here, they are not used, so we use 0,0 instead. *)
        let rule_combined =
          let simple_pred1 = match cl1.Ord.conclusion with
            | Pred(p,_) -> p
          in
          let simple_pred2 = match cl2.Ord.conclusion with
            | Pred(p,_) -> p
          in
          let hyp = [Pred(simple_pred1,inj_data1.arguments);Pred(simple_pred2,inj_data2.arguments)]
          and concl = Pred(pred_combined,inj_data1.arguments@inj_data2.arguments)
          and constra = { neq = [List.map2 (fun t1 t2 -> (t1,t2)) inj_data1.occurrences inj_data2.occurrences]; is_nat = []; is_not_nat = []; geq = [] } in
          Rule(-1,GoalInjective,hyp,concl,constra)
        in

        let constra_combined = generate_constra_occ (Terms.wedge_constraints cl1.Ord.constraints cl2.Ord.constraints) occ_concl1 occ_concl2 in
        let concl_combined = match cl1.Ord.conclusion,cl2.Ord.conclusion with
          | Pred(p1,args1), Pred(p2,args2) -> Pred(pred_combined,args1@args2)
        in

        let hist_combined =
          let inj =
            Terms.auto_cleanup (fun () ->
              if n1 >= 0 && n2 >= 0
              then DoubleIndex(n1,n2 + (List.length cl1.Ord.hypotheses))
              else if n1 >= 0
              then SingleIndex(copy_fact2 concl_combined, copy_fact2 ev2, n1)
              else if n2 >= 0
              then SingleIndex(copy_fact2 concl_combined, copy_fact2 ev1, n2 + (List.length cl1.Ord.hypotheses))
              else NoIndex(copy_fact2 concl_combined)
            )
          in

          HInjectivity(inj,Resolution(cl1.Ord.history,0,(Resolution(cl2.Ord.history,1,rule_combined))))
        in

        let clause =
          {
            Ord.hypotheses = cl1.Ord.hypotheses @ cl2.Ord.hypotheses;
            Ord.conclusion = concl_combined;
            Ord.history = hist_combined;
            Ord.constraints = constra_combined
          }
        in
        Ord.copy2 clause
      ) 
    in
    Terms.auto_cleanup (fun () ->
      let clauses = Rules.solving_request_rule ~close_equation:false lemmas injective_clause in
      if clauses != []
      then
        begin
          faulty_clauses_injective := clauses @ !faulty_clauses_injective;
          raise InjectivityUnverifiable
        end
    )
  with
    | Unify -> ()
    | InjectivityUnverifiable -> raise Unify

let check_injectivity restwork lemmas injectivity_data_op positive_clause = match injectivity_data_op,positive_clause with
  | None,_
  | Some _, None -> restwork () (* It can happen that there is injectivity_data but no positive clause. Eg : inj-A ==> inj-B || attacker *)
  | Some injectivity_data, Some (clause,occ_list,occ_concl) ->
      let old_inj_collector = !current_inj_collector in
      try
        (* We make a copy of the clause (because we need to check a clause vs herself) *)
        let (clause2, occ_list2, occ_concl2) =
          Terms.auto_cleanup (fun () ->
            let clause = Ord.copy2 clause in
            let occ_concl = List.map copy_term2 occ_concl in
            let occ_list = List.map (fun (i,(n,ev)) -> (i,(n,copy_fact2 ev))) occ_list in
            clause,occ_list, occ_concl
          )
        in

        (* We add this copy to the collector and we will do the tests with the first one. *)
        add_in_inj_collector clause2 occ_concl2 occ_list2 injectivity_data;
        let unify_found = ref false in
        (* We now compare the clause with the collector *)
        List.iter (fun (i1,ev1) ->
          let stored_clauses_list = IntMap.find i1 !current_inj_collector in
          (* Cannot raise Not_Found since the first copy was added in the collector *)
          List.iter (fun (ev2,cl2,occ_cl2,inj_data2) ->
            try
              compare_two_clauses lemmas (ev1,clause,occ_concl,injectivity_data) (ev2,cl2,occ_cl2,inj_data2)
            with Unify -> unify_found := true
          ) stored_clauses_list
        ) occ_list;
        if !unify_found
        then raise Unify
        else restwork ();
        current_inj_collector := old_inj_collector
      with Unify ->
        current_inj_collector := old_inj_collector;
        raise Unify

(* Matching functions *)

(* Note that for bievents, we do not need to check ordering functions since queries on bitraces
   do not contain ordering constraints. Hence conditions on ordering functions are trivially satisfied. *)
let rec match_event2 restwork (ev1_query,ev2_query) = function
  | [] -> raise Unify
  | (ev1,ev2)::q ->
      try
        TermsEq.unify_modulo_list restwork [ev1;ev2] [ev1_query;ev2_query]
      with Unify -> match_event2 restwork (ev1_query,ev2_query) q

let rec match_event2_list restwork ev_l hypl = match ev_l with
  | [] -> restwork ()
  | ev::q ->
      match_event2 (fun () ->
        match_event2_list restwork q hypl
      ) ev hypl

(* [match_event restwork ev_query ord_data_query occ_query hypl] tries to match the event [ev_query] from
   the query with the hypotheses in [hypl]. It takes into considering the ordering data [ord_data_query]
   and occurrence term [occ_query] from the query. *)
let rec match_event restwork ev_query ord_data_query occ_query = function
  | [] -> raise Unify
  | ((_,hyp) as p) ::q ->
      let Pred(pred,args) = HypOrd.get_fact hyp in
      if pred != Param.event_pred_block && pred != Param.inj_event_pred_block
      then Parsing_helper.internal_error __POS__ "[match_event] The list should only contain events.";

      try
        Ordering.verify_and_update_ordering_data_IO (fun () ->
          let list_query,list_event = match occ_query with
            | Some occ ->
                if pred == Param.inj_event_pred_block
                then [ev_query;occ], args
                else
                  (* All events with an occurrence in the query have the status WithOcc. Hence
                    if the predicate is event_pred_block then we know the two events cannot unify. *)
                  raise Unify
            | _ -> [ev_query], [List.hd args]
          in

          TermsEq.unify_modulo_list (fun () ->
            restwork p
          ) list_event list_query
        ) ord_data_query (HypOrd.get_ordering_relation hyp)
      with Unify -> match_event restwork ev_query ord_data_query occ_query q

let match_premise (restwork:unit->unit) (premise:fact) (concl:fact) = match premise,concl with
  | Pred(chann1, args1),Pred(chann2, args2) ->
      if chann1 != chann2 then Parsing_helper.internal_error __POS__ "[match_premise] Should have the same predicate.";
      TermsEq.unify_modulo_list restwork args1 args2

(* The function restwork takes as input a list of (k,ev,occ) where k is the injective index *)
let rec match_event_list restwork ev_l hypl = match ev_l with
  | [] -> restwork []
  | (None,ord_fun,occ,ev)::q_ev ->
      match_event (fun _ ->
        match_event_list (fun ind_occ_l  ->
          restwork ind_occ_l
        ) q_ev hypl
      ) ev ord_fun occ hypl
  | (Some k,ord_fun,occ,ev)::q_ev ->
      match_event (fun (i,hyp) ->
        match_event_list (fun ind_occ_l ->
          restwork ((k,(i,HypOrd.get_fact hyp))::ind_occ_l)
        ) q_ev hypl
      ) ev ord_fun occ hypl

let rec match_premise_nested_query restwork g_nested hypl = match g_nested with
  | [] -> restwork [] []
  | ((None,g_ord_fun,g_occ,g_ev),nested_concl)::q_ev ->
      match_event (fun (i,hyp) ->
        match_premise_nested_query (fun ind_occ_l matching_nested ->
          restwork ind_occ_l ((None,i,hyp,g_ord_fun,nested_concl)::matching_nested)
        ) q_ev hypl
      ) g_ev g_ord_fun g_occ hypl
  | ((Some k,g_ord_fun,g_occ,g_ev),nested_concl)::q_ev ->
      match_event (fun (i,hyp) ->
        match_premise_nested_query (fun ind_occ_l matching_nested ->
          restwork ((k,(i,HypOrd.get_fact hyp))::ind_occ_l) ((Some k,i,hyp,g_ord_fun,nested_concl)::matching_nested)
        ) q_ev hypl
      ) g_ev g_ord_fun g_occ hypl

let rec match_predicate (restwork:int -> unit) ((p,args,ord_data_query): predicate * term list * ordering_data ) = function
  | [] -> raise Unify
  | (n,hyp)::q ->
      match HypOrd.get_fact hyp with
        | Pred(p',args') -> 
            if p == Terms.unblock_predicate p'
            then
              try
                Ordering.verify_and_update_ordering_data_IO (fun () ->
                  TermsEq.unify_modulo_list (fun () ->
                    restwork n
                  ) args args'
                ) ord_data_query (HypOrd.get_ordering_relation hyp)
              with Unify -> match_predicate restwork (p,args,ord_data_query) q
            else match_predicate restwork (p,args,ord_data_query) q

(* The function restwork takes as input a list of non-blocking predicates to check *)
let rec match_predicate_list restwork pred_l hypl = match pred_l with
  | [] -> restwork []
  | (Pred(p,args),ord_data)::q ->
      begin
        try
          (* Try to see if the predicate is already included in the hypotheses *)
          match_predicate (fun _ ->
            match_predicate_list (fun pred_nonblock_to_check ->
              restwork pred_nonblock_to_check
            ) q hypl
          ) (p,args,ord_data) hypl
        with Unify ->
          if p.p_prop land Param.pred_BLOCKING != 0
          then raise Unify
          else
            match_predicate_list (fun pred_nonblock_to_check ->
              restwork ((Pred(p,args),ord_data)::pred_nonblock_to_check)
            ) q hypl
      end

let rec match_predicate_block restwork (p,args) = function
  | [] -> raise Unify
  | Pred(p',args')::q when p.p_prop land Param.pred_BLOCKING != 0 ->
      if p == p'
      then
        try
          TermsEq.unify_modulo_list (fun () ->
              restwork ()
          ) args args'
        with Unify -> match_predicate_block restwork (p,args) q
      else match_predicate_block restwork (p,args) q
  | _::q -> match_predicate_block restwork (p,args) q

let rec match_predicate_block_list pred_l hypl = match pred_l with
  | [] -> ()
  | Pred(p,args)::q when p.p_prop land Param.pred_BLOCKING != 0 ->
      match_predicate_block (fun () ->
        match_predicate_block_list q hypl
      ) (p,args) hypl
  | _ -> raise Unify

(* Trying to prove [g_pred_unblock] and [g_constra] from [pred_block_cl] and [pred_unblock_cl].
   When the proof succeeds, updates [crel_ord_opt] with the semantics in which
   the proof succeeded (with or without phase transitions) and 
   calls [f_next] with the constraints needed for this proof.
   [g_constra] only contains the disequalities that cannot be negated and thus should be checked. *)
let match_unblock_predicates_same_ord_fun f_next g_pred_unblock g_constra pred_unblock_cl pred_block_cl crel_ord_opt =
  assert (g_pred_unblock <> []);

  let prove_one get_clauses = 
    Terms.auto_cleanup (fun () ->
      let bad_fact = Pred(Param.bad_pred, []) in
      let pred_unblock_cl' = List.map Terms.copy_fact2 pred_unblock_cl in
      let pred_block_cl' = List.map Terms.copy_fact2 pred_block_cl in
      let g_pred_unblock' = List.map (fun (f,_) -> Terms.copy_fact2 f) g_pred_unblock in
      let g_constra' = Terms.copy_constra2 g_constra in
      Terms.cleanup();
      (* Let sigma_0 the substitution that replaces all variables by
        distinct constants. Let H => C the clause found by ProVerif.
        We show that we can prove an instance of the hypothesis of the query
        from \sigma_0 H. We should prove an instance of the hypothesis of the query
        from any instance of H. The derivation obtained using \sigma_0 H
        can converted into a derivation using \sigma H by replacing the
        constants with other terms. All steps remain valid except that
        the inequalities may no longer be true. Hence, we collect inequalities
        used in the derivation and further check that they are implied by
        the inequalities in H, by passing them to the function f. *)
      let unblocked_predicate_clauses =
        List.fold_left (fun acc fact -> match fact with
          | Pred(p,_) when p == Param.event2_pred_block || p == Param.event_pred_block || p == Param.inj_event_pred_block -> assert false
          | Pred({p_info = Block p;_},args) ->
              ([], Pred(p,args), Rule(-1, LblNone, [], Pred(p,args), Terms.true_constraints), Terms.true_constraints) :: acc
          | _ -> acc
        ) [] pred_block_cl'
      in
      let clauses =
        (g_pred_unblock', bad_fact, Rule(-1, LblNone, g_pred_unblock', bad_fact, g_constra'), g_constra') ::
        (get_clauses ()) @
        (List.map (fun fact -> ([], fact, Rule(-1, LblNone, [], fact, Terms.true_constraints), Terms.true_constraints)) pred_unblock_cl') @
        unblocked_predicate_clauses
      in
      Display.auto_cleanup_display (fun () ->
	(* Trying to prove [g_pred_unblock'] and [g_constra'] from [pred_block_cl'] and [pred_unblock_cl'] *)
        Display.Text.display_inside_query g_pred_unblock' g_constra' pred_block_cl' pred_unblock_cl';
        incr Param.inside_query_number;
        let inums = string_of_int (!Param.inside_query_number) in

        if !Param.html_output then
          begin
            Display.LangHtml.openfile ((!Param.html_dir) ^ "/inside" ^ inums ^ ".html") ("ProVerif: inside query " ^ inums);
            Display.Html.display_inside_query g_pred_unblock' g_constra' pred_block_cl' g_pred_unblock'
          end;
        (* the resolution prover must be _sound_ for this call
          while for other calls it must be _complete_.
          The function sound_bad_derivable is sound provided the clause
          do not contain "any_name". *)
        let cl_list = Rules.sound_bad_derivable clauses in
        try
          let cl =
            List.find (fun cl ->
              if Terms.is_true_constraints cl.Ord.constraints
              then 
                try 
                  match_predicate_block_list (List.map HypOrd.get_fact cl.Ord.hypotheses) pred_block_cl';
                  true
                with Unify -> false
              else false
            ) cl_list
          in
          (* Should I try other clauses in cl in case of subsequent failure?
            It may help, but that would be just by chance, since the clauses
            that use different inequalities on constants of \sigma_0 H
            in their derivation are typically removed by subsumption.
            Only clauses that have different hypotheses are kept. *)

          (* collect all inequalities in the derivation of cl_found *)
          let derivation = History.build_fact_tree cl.Ord.history in
          let g_constra'' = Reduction_helper.collect_constraints derivation in
          Reduction_helper.close_constraints g_constra'';
          begin
            (* Success: managed to prove the facts in hyp1_preds' *)
            Display.Text.display_inside_query_success g_constra'';

            if !Param.html_output
            then
              begin
                Display.Html.display_inside_query_success g_constra'';
                Display.LangHtml.close ();
                Display.Html.print_line ("<A HREF=\"inside" ^ inums ^ ".html\">Inside query: proof succeeded</A>")
              end;

            map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra''
          end
        with Not_found ->
          begin
            (* Failure: could not prove some fact in hyp1_preds' *)
            Display.Text.print_line "Inside query: proof failed";

            if !Param.html_output then
              begin
              Display.Html.print_line "Inside query: proof failed";
              Display.LangHtml.close();
              Display.Html.print_line ("<A HREF=\"inside" ^ inums ^ ".html\">Inside query: proof failed</A>")
              end;

            raise Unify
          end
      )
    )
  in

  try
    let constra = prove_one get_clauses_for_preds_Phaseless in
    (* The verification succeeds. *)
    Ordering.update_ordering_data_list_semantics (fun () ->
      f_next constra
    ) g_pred_unblock crel_ord_opt SemPhaseLess
  with Unify ->
    let constra = prove_one get_clauses_for_preds_Std in
    Ordering.update_ordering_data_list_semantics (fun () ->
      f_next constra
    ) g_pred_unblock crel_ord_opt SemStd

let exclusive_union vars_l1 vars_l2 = 
  let vars = ref vars_l1 in
  List.iter (fun v -> if List.memq v vars_l1 then raise Unify else vars := v :: !vars) vars_l2;
  !vars 

let check_distinct_existential_variables g_pred_unblock_partition =
  if List.length g_pred_unblock_partition > 1
  then
    let existential_variables_in_partitions =
      List.map (fun (_,fact_list) ->
        let vars = ref [] in
        List.iter (function (Pred(_,args),_) -> List.iter (Termslinks.get_vars vars) args) fact_list;
        !vars
      ) g_pred_unblock_partition
    in
    let _ = List.fold_left exclusive_union [] existential_variables_in_partitions in
    ()

(* Trying to prove [g_pred_unblock] and [g_constra] from [pred_block_cl] and [pred_unblock_cl].
   When the proof succeeds, calls [restwork] with the constraints needed for this proof. *)
let match_unblock_predicates restwork g_pred_unblock g_constra pred_unblock_cl pred_block_cl =
  if g_pred_unblock = []
  then restwork (map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra)
  else
    begin 
      (* We prove user-defined predicates by groups that have the same ordering function.
       [g_pred_unblock_partition] is a list of (ord_fun, predicates that have that ord_fun)
       in [g_pred_unblock]. *)

      let compare_g_pred (_,ord_data1) (_,ord_data2) = compare ord_data1.ord_target ord_data2.ord_target in
      let g_pred_unblock_sorted = List.sort compare_g_pred g_pred_unblock in

      let rec partition_g_pred cur_ord_fun cur_g_pred_acc = function
        | [] -> [cur_ord_fun,cur_g_pred_acc]
        | (fact,ord_data)::q when ord_data.ord_target = cur_ord_fun -> partition_g_pred cur_ord_fun ((fact,ord_data)::cur_g_pred_acc) q
        | (fact,ord_data)::q -> (cur_ord_fun,cur_g_pred_acc)::(partition_g_pred ord_data.ord_target [fact,ord_data] q)
      in

      let (fact,ord_data) = List.hd g_pred_unblock_sorted in
      let g_pred_unblock_partition = partition_g_pred ord_data.ord_target [fact,ord_data] (List.tl g_pred_unblock_sorted) in

      check_distinct_existential_variables g_pred_unblock_partition;

      let rec prove_through_g_pred f_next = function
        | [] -> f_next true_constraints
        | (g_ord_fun,g_preds)::q ->
            let gen_partition (acc_fact,acc_rel) (_,hyp) =
              let crel = HypOrd.get_ordering_relation hyp in
              Parsing_helper.debug (fun () ->
                Parsing_helper.debug_msg "-- Testing inclusion ";
                print_string "[DEBUG] Clause ";
                Ordering.Debug.display_clause_ordering_relation crel;
                print_string "\n";
                print_string "[DEBUG] Query ";
                Ordering.Debug.display_query_ordering_relation g_ord_fun;
                print_string "\n";
                Parsing_helper.debug_msg (Printf.sprintf "Result = %b" (Ordering.includes_query_clause g_ord_fun crel))
              );
              if Ordering.includes_query_clause g_ord_fun crel 
              then 
                let acc_rel' = match acc_rel with
                  | None -> Some crel
                  | Some v -> Some (Ordering.union_clause v crel)
                in 
                (HypOrd.get_fact hyp)::acc_fact,acc_rel'
              else (acc_fact,acc_rel)
            in
	    (* We want to prove [g_constra], [g_preds] and [g_ord_fun] from [pred_unblock_cl] and [pred_block_cl].
	       Each element of [pred_unblock_cl] and [pred_block_cl] comes with an ordering relation.
	       To guarantee [g_ord_fun], we must keep only the elements of [pred_unblock_cl] and [pred_block_cl]
	       whose ordering relation implies [g_ord_fun]. Furthermore, we collect in [crel_union2] the
	       union of ordering relations of kept elements of [pred_unblock_cl] and [pred_block_cl], 
	       which is guaranteed to hold in the proof of [g_constra] and [g_preds] and is stronger than 
	       [g_ord_fun]. *)
            let (pred_unblock_cl',crel_union1) = List.fold_left gen_partition ([],None) pred_unblock_cl in
            let (pred_block_cl',crel_union2) = List.fold_left gen_partition ([],crel_union1) pred_block_cl in

            match_unblock_predicates_same_ord_fun (fun constra -> 
              prove_through_g_pred (fun constra' ->
                f_next (wedge_constraints constra constra')
              ) q
            ) g_preds g_constra pred_unblock_cl' pred_block_cl' crel_union2
      in

      prove_through_g_pred restwork g_pred_unblock_partition
    end

(* [negate_predicate_constra] generates new clauses by negating the disequalities and inequalities.
   To obtain the correct history, we use HCaseDistinction to indicate how to obtain the negated disequalities and inequalities.
   We assume here that there is no disjunction of disequalities. Moreover we assume that there is no is_not_nat predicate
   to negate.
   Note: the constraints [g_constra_to_negate] are closed under the equational theory before calling this function.
 *)

let negate_predicate_constra id_thread lemmas cl (* (hypl,concl,hist,constra) *) g_constra_to_negate =
  assert (g_constra_to_negate.is_not_nat == []);

  let accu = ref [] in

  List.iter (fun t ->
    let t' = specvar_to_var (TermsEq.remove_syntactic_term t) in

    let hist' =
      Terms.auto_cleanup (fun () ->
        let concl'' = Terms.copy_fact2 cl.Ord.conclusion in
        let hypl'' = List.map (fun h -> Terms.copy_fact2 (HypOrd.get_fact h)) cl.Ord.hypotheses in
        let t'' = Terms.copy_term2 t' in
        HCaseDistinction(concl'',hypl'',[],(Terms.constraints_of_is_not_nat t''), cl.Ord.history)
      )
    in
    let clause1 = { cl with history = hist'; constraints = { cl.Ord.constraints with is_not_nat = t'::cl.Ord.constraints.is_not_nat }} in
    let clause2 = Terms.auto_cleanup (fun () -> Ord.copy2 clause1 ) in

    Terms.auto_cleanup (fun () ->
      let ord_rules = Rules.solving_request_rule ~close_equation:false lemmas clause2 in
      accu := List.rev_append ord_rules !accu
    )
  ) g_constra_to_negate.is_nat;

  List.iter (fun (t1,n,t2) ->
    let t1' = specvar_to_var (TermsEq.remove_syntactic_term t1) in
    let t2' = specvar_to_var (TermsEq.remove_syntactic_term t2) in

    (* We generate the histories of the three cases.
        - hist1 is the history when t1 is not a natural number
        - hist2 is the history when t2 is not a natural number
        - hist3 is the history where t1 + n < t2, i.e. t2 - n - 1 >= t1 *)
    let (hist1, hist2, hist3) =
      Terms.auto_cleanup (fun () ->
        let concl'' = Terms.copy_fact2 cl.Ord.conclusion in
        let hypl'' = List.map (fun h -> Terms.copy_fact2 (HypOrd.get_fact h)) cl.Ord.hypotheses in
        let t1'' = Terms.copy_term2 t1' in
        let t2'' = Terms.copy_term2 t2' in
        HCaseDistinction(concl'',hypl'',[],(Terms.constraints_of_is_not_nat t1''), cl.Ord.history),
        HCaseDistinction(concl'',hypl'',[],(Terms.constraints_of_is_not_nat t2''), cl.Ord.history),
        HCaseDistinction(concl'',hypl'',[],{ neq = []; is_nat = []; is_not_nat = []; geq = [t2'',(-n-1),t1'']}, cl.Ord.history)
      )
    in

    let clause1 = { cl with history = hist1; constraints = { cl.Ord.constraints with is_not_nat = t1'::cl.Ord.constraints.is_not_nat } } in
    let clause2 = { cl with history = hist2; constraints = { cl.Ord.constraints with is_not_nat = t2'::cl.Ord.constraints.is_not_nat } } in
    let clause3 = { cl with history = hist3; constraints = { cl.Ord.constraints with geq = (t2',(-n-1),t1')::cl.Ord.constraints.geq } } in

    List.iter (fun cl ->
      let cl' = Terms.auto_cleanup (fun () -> Ord.copy2 cl) in
      Terms.auto_cleanup (fun () ->
        let ord_rules = Rules.solving_request_rule ~close_equation:false lemmas cl' in
        accu := List.rev_append ord_rules !accu
      )
    ) [clause1;clause2;clause3]
  ) g_constra_to_negate.geq;

  List.iter (function
    | [t,t'] ->
        (* [t] and [t'] are both ground. The variables specvar are the free variables of
           [concl] or [hypl] *)
        let t1 = specvar_to_var (TermsEq.remove_syntactic_term t) in
        let t1' = specvar_to_var (TermsEq.remove_syntactic_term t') in

        (* Retreive the free variables. They should be contained the variables of [concl] and [hypl]. *)
        let free_vars = ref [] in
        Terms.get_vars_acc free_vars t1;
        Terms.get_vars_acc free_vars t1';

        begin
          try
            TermsEq.unify_modulo (fun () ->
              (* Retrieve the substitution *)
              let subst =
                List.fold_left (fun acc x -> match x.link.(id_thread) with
                  | NoLink -> acc
                  | TLink t -> (x,TermsEq.remove_syntactic_term t)::acc
                  | _ -> Parsing_helper.internal_error __POS__ "[negate_predicate_constra] Unexpected link."
                ) [] !free_vars
              in

              (* Remove the link to copy the history *)
              List.iter (fun (x,_) -> x.link.(id_thread) <- NoLink) subst;
              let hist' =
                Terms.auto_cleanup (fun () ->
                  let concl' = Terms.copy_fact2 cl.Ord.conclusion in
                  let hypl' = List.map(fun h -> Terms.copy_fact2 (HypOrd.get_fact h)) cl.Ord.hypotheses in
                  let subst' = List.map (fun (x,t) -> Terms.copy_term2 (Var x), Terms.copy_term2 t) subst in
                  HCaseDistinction(concl',hypl',subst',Terms.true_constraints,cl.Ord.history)
                )
              in
              (* Relink the variables *)
              List.iter (fun (x,t) -> x.link.(id_thread) <- TLink t) subst;

              let clause1 = { cl with history = hist' } in
              let clause2 = Terms.auto_cleanup (fun () -> Ord.copy2 clause1 ) in
              Terms.auto_cleanup (fun () ->
                let ord_rules = Rules.solving_request_rule ~close_equation:false lemmas clause2 in
                accu := List.rev_append ord_rules !accu;
                (* We raise Unify to ensure that all substitutions are applied *)
                raise Unify
              )
            ) t1 t1'
          with Unify ->
            (* Unify is always raised. *)
            ()
        end
    | _ -> Parsing_helper.internal_error __POS__ "[negate_predicate_constra] Disequalities should not contain disjunction at this point."
  ) g_constra_to_negate.neq;

  !accu

(* We distinguish cases depending on whether [g_constra_to_add] are true or not.

   [generate_positive_clauses clause occ_concl occ_list g_constra_to_add] returns either [None] or [Some(clause')],
   where [clause'] is [clause] with the disequalities [g_constra_to_add] added
   in the hypothesis.
    The function raises [Unify] when no clause can be generated, i.e. hypotheses are false.
    The function returns [None] when there is no injectivity to check. This
    is due to the fact that we do not need to store the positive clause when there is no injectivity to check.

    Notes:
    - the constraints [g_constra_to_add] are closed under the equational theory before calling this function.
    - [negate_predicate_constra] deals with the other case by negating the constraints. *)
let generate_positive_clauses cl occ_concl occ_list g_constra_to_add =
  let g_constra_to_add1 = Terms.map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra_to_add in
  let occ_list1 = List.map (fun (i,(n,ev)) -> (i,(n,specvar_to_var_fact (TermsEq.remove_syntactic_fact ev)))) occ_list in
  let occ_concl1 = List.map (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) occ_concl in

  (* Check if the hypotheses of the new clause are satisfiable *)
  if not (Terms.is_true_constraints g_constra_to_add)
  then
    Terms.auto_cleanup (fun () ->
      (* Check if the hypotheses of the new clause are satisfiable *)
      let clause = { cl with Ord.constraints = Terms.wedge_constraints cl.Ord.constraints g_constra_to_add1 } in
      if Rules.is_hypothesis_unsatisfiable clause
      then raise Unify
    );

  if occ_list = []
  then None
  else
    let hist' =
      if Terms.is_true_constraints g_constra_to_add
      then cl.Ord.history
      else
        Terms.auto_cleanup (fun () ->
          let concl' = Terms.copy_fact2 cl.Ord.conclusion in
          let hypl' = List.map(fun h -> Terms.copy_fact2 (HypOrd.get_fact h)) cl.Ord.hypotheses in
          let constra' = Terms.copy_constra2 g_constra_to_add1 in
          HCaseDistinction(concl',hypl',[],constra',cl.Ord.history)
        )
    in

    let clause1 = { cl with Ord.history = hist'; Ord.constraints = Terms.wedge_constraints cl.Ord.constraints g_constra_to_add1 } in

    Terms.auto_cleanup (fun () ->
      let clause = Ord.copy2 clause1 in
      let occ_concl = List.map copy_term2 occ_concl1 in
      let occ_list = List.map (fun (i,(n,ev)) -> (i,(n,copy_fact2 ev))) occ_list1 in
      Some (clause,occ_list, occ_concl)
    )

(* Generation of instantiated nested queries and the associated rules *)

let apply_ordering_function_on_event ord_data = function
  | QSEvent(inj_op,ord_data',occ,ev) ->
      QSEvent(inj_op,{ ord_target = Ordering.intersection_query ord_data'.ord_target ord_data.ord_target; ord_proved = ref None; temp_var = None},occ,ev)
  | QFact(p,ord_data',args) ->
      if Ordering.can_predicate_have_query_ordering_relation p
      then QFact(p,{ ord_target = Ordering.intersection_query ord_data'.ord_target ord_data.ord_target; ord_proved = ref None; temp_var = None},args)
      else QFact(p,Ordering.generate_empty_ordering_data (),args)
  | g_ev -> g_ev

let conclusion_query_of_constra constra =
  let concl1 =
    List.fold_left (fun acc_q neq_l -> match neq_l with
      | [t1,t2] -> Reduction_helper.make_qand acc_q (QEvent(QNeq((t1, Parsing_helper.dummy_ext),(t2, Parsing_helper.dummy_ext))))
      | _ -> Parsing_helper.internal_error __POS__ "[conclusion_query_of_constra] The constraint obtained from the query should not have disjunctions of inequalities."
    ) QTrue constra.neq
  in
  let concl2 =
    List.fold_left (fun acc_q (t1,i,t2) ->
      Reduction_helper.make_qand acc_q (QEvent(QGeq((sum_nat_term t1 i, Parsing_helper.dummy_ext),(t2, Parsing_helper.dummy_ext))))
    ) concl1 constra.geq
  in
  let concl3 =
    List.fold_left (fun acc_q t ->
      Reduction_helper.make_qand acc_q (QEvent(QIsNat t))
    ) concl2 constra.is_nat
  in
  concl3

let rec apply_ordering_function_on_conclusion ord_fun = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints _ as q -> q (* this deals with ordering, hence irrelevant for the constraints *)
  | QEvent(ev) -> QEvent(apply_ordering_function_on_event ord_fun ev)
  | NestedQuery(Before([ev],concl)) ->
      NestedQuery(Before([apply_ordering_function_on_event ord_fun ev],concl))
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[apply_ordering_function_on_conclusion] Nested queries should have exactly one event in their premise."
  | QAnd(concl1,concl2) ->
      QAnd(apply_ordering_function_on_conclusion ord_fun concl1,apply_ordering_function_on_conclusion ord_fun concl2)
  | QOr(concl1,concl2) ->
      QOr(apply_ordering_function_on_conclusion ord_fun concl1,apply_ordering_function_on_conclusion ord_fun concl2)

let generate_nested_query_and_rule g_premise g_ev g_constra_to_check g_constra_to_add g_pred matching_nested cl (* ((hypl,concl,hist,constra):auth_ordered_reduction)*) =

  (* We build  the query *)
  let (g_premise_no_constra,g_premise_constra) = 
    List.partition (function
      | QNeq _ | QGeq _ | QIsNat _ -> false
      | _ -> true
    ) g_premise
  in

  let nb_fact_in_premise = List.length g_premise_no_constra in

  let premise_from_nested =
    List.map (fun (_,_,hyp,_,_) -> match HypOrd.get_fact hyp with
      | Pred(f,[evt;occ]) when f == Param.inj_event_pred_block -> QSEvent(None,Ordering.generate_empty_ordering_data (),Some occ,evt)
      | Pred(f,[evt]) -> QSEvent(None,Ordering.generate_empty_ordering_data (),None,evt)
      | _ -> Parsing_helper.internal_error __POS__ "[generate_nested_query_and_rule] Expecting an event or injective event."
    ) matching_nested
  in
  let new_g_premise = g_premise_no_constra @ premise_from_nested @ g_premise_constra in

  let new_q_concl1 =
    List.fold_left (fun acc_q (inj_op,ord_data,occ,ev) ->
      Reduction_helper.make_qand acc_q (QEvent(QSEvent(inj_op,ord_data,occ,ev)))
    ) QTrue g_ev
  in
  (* Difference with respect to the paper: we add the matched events also to the
     conclusion of the query that we generate. That uniformizes the verification
     of injectivity, which looks only at the conclusion of the query. *)
  let new_q_concl2 =
    List.fold_left (fun acc_q (inj_op,_,hyp,ord_data_query,_) -> match HypOrd.get_fact hyp with
      | Pred(f,[evt;occ]) when f == Param.inj_event_pred_block -> Reduction_helper.make_qand acc_q (QEvent(QSEvent(inj_op,ord_data_query,Some occ,evt)))
      | Pred(f,[evt]) ->
          assert(inj_op = None);
          Reduction_helper.make_qand acc_q (QEvent(QSEvent(None,ord_data_query,None,evt)))
      | _ -> Parsing_helper.internal_error __POS__ "[generate_nested_query_and_rule] Expecting an event or injective event."
    ) new_q_concl1 matching_nested
  in
  let new_q_concl3 =
    List.fold_left (fun acc_q (Pred(p,args),ord_fun) ->
      Reduction_helper.make_qand acc_q (QEvent(QFact(p,ord_fun,args)))
    ) new_q_concl2 g_pred
  in
  let (new_q_concl4,_) =
    List.fold_left (fun (acc_q,i) (_,_,_,ord_fun_query,concl_nested) ->
      let new_ord_target = match ord_fun_query.ord_target with
        | QOSpecific l -> QOSpecific (l@[i,(SemStd,Leq)])
        | _ -> QOSpecific ([i,(SemStd,Leq)])
      in
      let ord_fun_query' = { ord_target = new_ord_target; ord_proved = ref None; temp_var = None } in
      let concl_nested' = apply_ordering_function_on_conclusion ord_fun_query' concl_nested in
      let acc_q' = Reduction_helper.make_qand acc_q concl_nested' in
      (acc_q',i+1)
    ) (new_q_concl3,nb_fact_in_premise + 1) matching_nested
  in
  let new_q_concl5 = Reduction_helper.make_qand new_q_concl4 (conclusion_query_of_constra g_constra_to_check) in

  let new_query =
    Terms.auto_cleanup (fun () ->
      let q1 = Before(new_g_premise,new_q_concl5) in
      let q2 = copy_query q1 in
      Query.map_term_realquery Terms.specvar_to_var q2
    )
  in

  (* We build the clause *)

  let g_constra_to_add1 = Terms.map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra_to_add in
  
  let fact_for_hyp =
    List.mapi (fun i (_,_,hyp,_,_) -> 
      let hyp' = HypOrd.map_fact (fun fact -> specvar_to_var_fact (TermsEq.remove_syntactic_fact fact)) hyp in
      HypOrd.create_nested_hypothesis_nth_conclusion hyp' nb_fact_in_premise (i+1)
    ) matching_nested
  in
  let new_hypl = cl.Ord.hypotheses @ fact_for_hyp in

  let (pred_for_concl,args_for_concl) =
    List.fold_right (fun hyp (acc_p,acc_a)->
      let Pred(p,args) = HypOrd.get_fact hyp in
      (p::acc_p,args@acc_a)
    ) fact_for_hyp ([],[])
  in

  let (new_concl,nb_fact_in_orig_concl) = match cl.Ord.conclusion with
    | Pred({ p_info = Combined(nb_std,nb_user,p_list); _}, args) ->
        let new_combined_pred = Param.get_pred (Combined(nb_std,nb_user,p_list@pred_for_concl)) in
	(* we use [nb_std] and [nb_user] on purpose: they are the number of standard and
           user-defined predicates in the *initial* query, not the nested query *)
        Pred(new_combined_pred,args@args_for_concl), List.length p_list
    | Pred({ p_info = UserPred _;_} as p,args) ->
        let new_combined_pred = Param.get_pred (Combined(0,1,p::pred_for_concl)) in
        Pred(new_combined_pred,args@args_for_concl), 1
    | Pred(p,args) ->
        let new_combined_pred = Param.get_pred (Combined(1,0,p::pred_for_concl)) in
        Pred(new_combined_pred,args@args_for_concl), 1
  in

  (* Clause used for generating the history *)
  let rule_nested =
    let (old_concl_pred,args_old_concl_pred) = match cl.Ord.conclusion with
      | Pred(p,_) -> p, List.map Terms.new_var_def_term p.p_type
    in
    let (fresh_fact_for_hyp, args_for_hyp) =
      List.fold_right (fun hyp (acc_f,acc_a) ->
        let Pred(p,_) = HypOrd.get_fact hyp in
        let args = List.map Terms.new_var_def_term p.p_type in
        Pred(p,args)::acc_f, args@acc_a
      ) fact_for_hyp ([],[])
    in
    let concl_rule = match new_concl with
      | Pred(p,_) -> Pred(p,args_old_concl_pred@args_for_hyp)
    in
    let hyp_rule = Pred(old_concl_pred,args_old_concl_pred)::fresh_fact_for_hyp in

    Rule(-1,GenerationNested,hyp_rule,concl_rule,Terms.true_constraints)
  in

  let new_hist1 =
    if Terms.is_true_constraints g_constra_to_add
    then cl.Ord.history
    else
      Terms.auto_cleanup (fun () ->
        let concl' = Terms.copy_fact2 cl.Ord.conclusion in
        let hypl' = List.map(fun h -> Terms.copy_fact2 (HypOrd.get_fact h)) cl.Ord.hypotheses in
        let constra' = Terms.copy_constra2 g_constra_to_add1 in
        HCaseDistinction(concl',hypl',[],constra',cl.Ord.history)
      )
  in
  let new_hist2 = HNested(List.map (fun (_,i,_,_,_) -> i) matching_nested, nb_fact_in_orig_concl, Resolution(new_hist1,0,rule_nested)) in
  let new_clause = 
    Terms.auto_cleanup (fun () ->
      Ord.copy2 {
        Ord.hypotheses = new_hypl;
        Ord.conclusion = new_concl;
        Ord.history = new_hist2;
        Ord.constraints = Terms.wedge_constraints cl.Ord.constraints g_constra_to_add1
      } 
     ) 
  in

  (new_query,new_clause)

(* val eval_gather : events -> Nested queries -> disequalities -> predicates  -> () -> .... *)
(* We assume that the matching has been done on the premise of the query *)

let rec eval_gather_event restwork = function
  | QEq((t1,_),(t2,_)) ->
      TermsEq.unify_modulo (fun () ->
        restwork [] [] Terms.true_constraints [] []
      ) t1 t2
  | QGeq((t1,_),(t2,_)) -> restwork [] [] (Terms.constraints_of_geq t1 t2) [] []
  | QIsNat t -> restwork [] [] (Terms.constraints_of_is_nat t) [] []
  | QNeq((t1,_),(t2,_)) -> restwork [] [] (Terms.constraints_of_neq t1 t2) [] []
  | QSEvent(inj_op,ord_data,occ,ev) -> restwork [inj_op,ord_data,occ,ev] [] Terms.true_constraints [] []
  | QSEvent2(ord_data,ev1,ev2) -> restwork [] [] Terms.true_constraints [] [ev1,ev2]
  | QFact(p,ord_data,args) -> restwork [] [] Terms.true_constraints [Pred(p,args),ord_data] []
  | QGr _ -> Parsing_helper.internal_error __POS__ "[eval_gather_event] Queries with strict inequalities should be encoded by now."
  | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "[eval_gather_event] Queries with max inequalities should not occur."

and eval_gather_conclusion restwork = function
  | QTrue -> restwork [] [] Terms.true_constraints [] []
  | QFalse -> raise Unify
  | QConstraints q -> restwork [] [] q [] []
  | QEvent(ev) -> eval_gather_event restwork ev
  | NestedQuery(Before([QSEvent(inj_op,ord_fun,occ,ev)],concl)) -> restwork [] [(inj_op,ord_fun,occ,ev),concl] Terms.true_constraints [] []
  | NestedQuery _ -> internal_error __POS__ "[eval_gather_conclusion] Nested query should have exactly one event in their premise."
  | QAnd(concl1,concl2) ->
      eval_gather_conclusion (fun g_ev1 g_nested1 g_constra1 g_pred1 g_bi_ev1 ->
        eval_gather_conclusion (fun g_ev2 g_nested2 g_constra2 g_pred2 g_bi_ev2 ->
          restwork (g_ev1@g_ev2) (g_nested1@g_nested2) (Terms.wedge_constraints g_constra1 g_constra2) (g_pred1@g_pred2) (g_bi_ev1@g_bi_ev2)
        ) concl2
      ) concl1
  | QOr(concl1,concl2) ->
      try
        eval_gather_conclusion restwork concl1
      with Unify ->
        eval_gather_conclusion restwork concl2

let rec clause_match_realquery id_thread restwork lemmas initial_nb_premise clause (* (((hyp,concl,_,constra) as clause):auth_ordered_reduction) *) = function
  | Before(evl_premise,concl_q) ->
      let evl_premise_no_constra = 
        List.filter (function
          | QNeq _ | QGeq _ | QIsNat _ -> false
          | _ -> true
        ) evl_premise
      in

      let (nb_std,nb_user) = match clause.Ord.conclusion with
        | Pred({ p_info = Combined(nb_std,nb_user,_); _},_) -> nb_std,nb_user
        | Pred({ p_info = UserPred _; _},_) -> 0,1
        | _ -> 1,0
      in

      (* Replace all variables in the clause with constants "SpecVar" *)
      assert (!current_bound_vars == []);
      Ord.iter_term Terms.put_constants clause;
      let clause' = Ord.copy2 clause in
      cleanup ();

      let constra_cl_for_implies = map_constraints TermsEq.remove_syntactic_term clause.constraints in
      let facts_for_implies =
        (TermsEq.remove_syntactic_fact clause.conclusion) ::
        List.map (fun hyp -> TermsEq.remove_syntactic_fact (HypOrd.get_fact hyp)) clause.hypotheses
      in
      let vars_for_implies = lazy (get_vars_fact_list facts_for_implies) in

      (* To prove the events and blocking predicates of the query (hyp1_events), we
         show that they match the events and blocking predicates of the clause (hyp2_events).
         These predicates cannot be derived from clauses.
         To prove the non-blocking predicate of the query (hyp1_preds), we
         show that they are derivable from any predicates (blocking or not) of the clause
         (hyp2_preds, hyp2_preds_block).
         These predicates cannot be directly in the clause since they are not blocking.

         Index in the list starts at 0.*)
      let (hyp_events,hyp_preds,hyp_preds_block,hyp_events2,_) =
        List.fold_left (fun (evl,pl,pbl,ev2l,n) hyp -> match HypOrd.get_fact hyp with
          | Pred(p,_)  when p == Param.event_pred_block || p == Param.inj_event_pred_block ->
              (n,hyp)::evl, pl, pbl, ev2l, n+1
          | Pred(p,[ev1;ev2]) when p == Param.event2_pred_block ->
              evl,pl,pbl,(ev1,ev2)::ev2l,n+1
          | Pred(p,_) when p.p_prop land Param.pred_BLOCKING != 0 ->
              evl,pl,(n,hyp)::pbl, ev2l, n+1
          | _ ->
              evl,(n,hyp)::pl,pbl,ev2l, n+1
        ) ([],[],[],[],0) clause'.hypotheses
      in

      (* Adding the events and predicates of the conclusion *)
      let to_add_in_hypl, occ_concl = occurrence_and_hyp_of_conclusion_predicate initial_nb_premise evl_premise_no_constra clause'.conclusion in

      let (to_add_in_hypl_events,to_add_in_hypl_preds,to_add_in_hypl_events2) =
        List.fold_left (fun (evl,pl,ev2l) (n,hyp) -> match HypOrd.get_fact hyp with
          | Pred(p,_) when p == Param.event_pred_block || p == Param.inj_event_pred_block -> (n,hyp)::evl, pl, ev2l
          | Pred(p,[ev1;ev2]) when p == Param.event2_pred_block -> evl,pl,(ev1,ev2)::ev2l
          | pred -> evl,(n,hyp)::pl,ev2l
        ) ([],[],[]) to_add_in_hypl
      in

      (* Retrieve the combined predicate for the premise *)

      let (_,premise,_,_) = event_list_to_rule (nb_std,nb_user) evl_premise_no_constra in
      let injectivity_data = generate_injective_data evl_premise_no_constra in

      try
        (* Unification of the conclusion of the clause with the premise of the query. *)
        match_premise (fun () ->
          (* Gather the different elements of the query *)
          eval_gather_conclusion (fun g_ev g_nested g_constra g_pred g_ev2 ->
            (* Match the events of biprocess *)
            match_event2_list (fun () ->
              (* Match the events *)
              match_event_list (fun occ_l_ev ->
                (* [occ_l_ev] is the list of (k,(n,ev)) where k is the injective index, ev the matched event
                   (including its occurrence name), n its position in the clause, for injective events *)
                match_premise_nested_query (fun occ_l_nested matching_nested ->
                  (* [occ_l_nested] is the list of (k,(n,ev)) where k is the injective index, ev the matched event
                     (including its occurrence name), n its position in the clause, for injective events
                     [matching_nested] is the list of (n,ev,ord_fun_hyp,ord_fun_query,concl_nested)
                     ([n] is an in [occ_l_nested] above)
                  *)
                  let occ_l = List.rev_append occ_l_nested occ_l_ev in

                  (* Match the predicates *)
                  match_predicate_list (fun g_pred_unblock_to_check ->
                    (* Close the gathered constraints modulo the equational theory, i.e. the inequalities and is_nat
                       predicates *)
                    TermsEq.close_constraints_eq_synt (fun g_constra2 ->
                      (* Split the disequalities that can be negated. When a disequality only contains
                         variables of the clause, it should be in fact ground at this stage since all
                         variables of the clause have been replaced by constants. *)
                      let filter_neq = List.exists (fun (t1,t2) -> Termslinks.has_vars t1 || Termslinks.has_vars t2) in
                      let filter_geq (t1,_,t2) = Termslinks.has_vars t1 || Termslinks.has_vars t2 in

                      let implies_constraints g_constra3 =
                        let g_constra4 = map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra3 in
                        TermsEq.implies_constraints None(*we could also use [vars_for_implies], it does not really matter*) constra_cl_for_implies g_constra4
                      in

                      let (g_constra_to_check, g_constra_to_negate) =
                        let (neq_check,neq_negate) = List.partition filter_neq g_constra2.neq in
                        let neq_negate' = List.filter (fun neq -> not (implies_constraints { neq = [neq]; is_nat = []; is_not_nat = []; geq = []})) neq_negate in
                        let (is_nat_check,is_nat_negate) = List.partition Termslinks.has_vars g_constra2.is_nat in
                        let is_nat_negate' = List.filter (fun is_nat -> not (implies_constraints { neq = []; is_nat = [is_nat]; is_not_nat = []; geq = []})) is_nat_negate in
                        let (geq_check,geq_negate) = List.partition filter_geq g_constra2.geq in
                        let geq_negate' = List.filter (fun geq -> not (implies_constraints { neq = []; is_nat = []; is_not_nat = []; geq = [geq]})) geq_negate in
                        { neq = neq_check; is_nat = is_nat_check; is_not_nat = []; geq = geq_check },
                        { neq = neq_negate'; is_nat = is_nat_negate'; is_not_nat = []; geq = geq_negate' }
                      in

                      let positive_clause_op = generate_positive_clauses clause occ_concl occ_l g_constra_to_negate in

                      (* Check injectivity conditions: We need check injectivity on the clause with
                         the disequalities and predicates that can be negated. We apply this test before checking unblock predicates
                         and nested queries. It should be faster than to do it later on. Moreover, it is sound because the check
                         of nested queries and unblock predicates do not modify the clause nor does it add disequalities or blocking
                         predicates to negate. *)
                      check_injectivity (fun () ->
                        (* Match the non blocking predicate *)
                        match_unblock_predicates (fun g_constra_to_check' ->
                          begin
                            try
                              let implying_constra = wedge_constraints (map_constraints (fun t -> specvar_to_var (TermsEq.remove_syntactic_term t)) g_constra_to_negate) constra_cl_for_implies in
                              TermsEq.simplify_constraints_continuation (Some (fun () -> Lazy.force vars_for_implies)) (fun c ->
                                if not (TermsEq.implies_constraints (Some (fun () -> Lazy.force vars_for_implies)) c g_constra_to_check')
                                then raise NoMatch
                              ) (fun c ->
                                let facts'' = List.map copy_fact4 facts_for_implies in
                                let vars_op = Some (fun () -> Terms.get_vars_fact_list facts'') in
                                if not (TermsEq.implies_constraints4 vars_op c g_constra_to_check')
                                then raise NoMatch
                              ) implying_constra
                            with NoMatch | TermsEq.FalseConstraint -> raise Unify
                          end;

                          let new_clauses_to_check = negate_predicate_constra id_thread lemmas clause g_constra_to_negate in

                          (* Instantiate the nested queries with the value given by the clause *)
                          if matching_nested = []
                          then Terms.auto_cleanup (fun () -> restwork new_clauses_to_check)
                          else
                            let (nested_query,request_clause) = generate_nested_query_and_rule evl_premise g_ev g_constra_to_check g_constra_to_negate g_pred matching_nested clause in
                            if injectivity_data = None
                            then
                              if Terms.auto_cleanup (fun () -> True = check_query ~close_equation:false ~contain_nested:true id_thread None lemmas initial_nb_premise request_clause nested_query)
                              then Terms.auto_cleanup (fun () -> restwork new_clauses_to_check)
                              else raise Unify
                            else
                              if True != Terms.auto_cleanup (fun () -> check_inj_query ~close_equation:false ~contain_nested:true id_thread (fun () -> restwork new_clauses_to_check) (fun _ -> DontKnow) lemmas initial_nb_premise request_clause nested_query)
                              then raise Unify
                        ) g_pred_unblock_to_check g_constra_to_check hyp_preds hyp_preds_block
                      ) lemmas injectivity_data positive_clause_op
                    ) g_constra
                  ) g_pred (hyp_preds_block@hyp_preds@to_add_in_hypl_preds)
                ) g_nested (hyp_events@to_add_in_hypl_events)
              ) g_ev (hyp_events@to_add_in_hypl_events)
            ) g_ev2 (hyp_events2@to_add_in_hypl_events2)
          ) concl_q;
        ) premise clause'.conclusion;
        true
      with Unify -> false

and check_non_inj_clauses id_thread display_attack_opt query lemmas initial_nb_premise clauses =
  let queue = ref clauses in
  let final_result = ref True in
  let size_queue = ref (List.length !queue) in
  let count_verified_clauses = ref 0 in
  let count_failed_clauses = ref 0 in
  Ordering.initialise_recording query;
  Display.Text.print_string "Starting verification.\n";
  flush_all ();

  let string_of_stats () = 
    Printf.sprintf "Clauses verified: %d. Clauses remaining: %d. Failed clauses: %d."
      !count_verified_clauses !size_queue !count_failed_clauses
  in

  let rec verify_queue () = match !queue with
    | [] -> !final_result
    | cl::q ->
        if !count_verified_clauses mod 200 = 0
        then 
          begin
            Display.Text.print_string (string_of_stats ());
            Display.Text.newline ()
          end;

        if 
          clause_match_realquery id_thread (fun clauses' -> 
            queue := clauses' @ q; 
            incr count_verified_clauses;
            size_queue := !size_queue - 1 + List.length clauses';
            (* We save the proved ordering *)
            Ordering.record_proved_ordering ()
          ) lemmas initial_nb_premise cl query
        then 
          begin
            Ordering.update_proved_ordering ();
            verify_queue ()
          end
        else
          match display_attack_opt with
            | None -> DontKnow
            | Some display_attack ->
                Ordering.cleanup_proved_ordering_when_not_true ();
                let result_display = display_attack cl in
                if result_display = DontKnow
                then
                  begin
                    final_result := DontKnow;
                    queue := q;
                    incr count_verified_clauses;
                    incr count_failed_clauses;
                    size_queue := !size_queue - 1;
                    if (!traces_to_reconstruct != 0) && (!Param.reconstruct_derivation) 
                    then verify_queue ()
                    else DontKnow
                  end
                else result_display
  in
  let res = verify_queue () in
  Ordering.cleanup_ordering ();
  res

and check_query ?(close_equation=true) ?(contain_nested=false) id_thread display_attack_opt lemmas initial_nb_premise request_rule query =
  let solved_rules = Rules.solving_request_rule ~close_equation:close_equation lemmas request_rule in

  let solved_rules' =
    (* Remove clauses subsumed modulo equational theory, when the query is not nested.
       (When it is nested, we keep them to generate enough clauses in sub-queries.) *)
    if !Param.simpeq_final && TermsEq.hasEquations() && not contain_nested then
      begin 
        Display.Text.print_string "Removing subsumed clauses modulo the equational theory.\n";
        flush_all ();
        remove_subsumed_mod_eq solved_rules
      end
    else
      solved_rules
  in

  let result = check_non_inj_clauses id_thread display_attack_opt query lemmas initial_nb_premise solved_rules' in
  if result = True
  then success_clauses := solved_rules' @ (!success_clauses);

  result

and check_inj_clauses id_thread restwork query lemmas initial_nb_premise clauses =
  let query' = Terms.auto_cleanup (fun () -> copy_query query) in
  match clauses with
    | [] ->
        begin
          try
            restwork ();
            true
          with Unify -> false
        end
    | cl::cll ->
        (* For injective queries, it is important that the [additional_clauses]
           generated by [clause_match_realquery] are checked in the [restwork] part
           of [clause_match_realquery]. *)
        clause_match_realquery id_thread (fun additional_clauses ->
          Terms.auto_cleanup (fun () ->
            if not (check_inj_clauses id_thread restwork query lemmas initial_nb_premise (additional_clauses@cll))
            then raise Unify
          )
        ) lemmas initial_nb_premise cl query'

and check_inj_query ?(close_equation=true) ?(contain_nested=false) id_thread restwork display_attack lemmas initial_nb_premise request_rule query =
  let solved_rules = Rules.solving_request_rule ~close_equation:close_equation lemmas request_rule in
  let solved_rules' =
    (* Remove clauses subsumed modulo equational theory, when the query is not nested.
       (When it is nested, we keep them to generate enough clauses in sub-queries.) *)
    if !Param.simpeq_final && TermsEq.hasEquations() && not (contain_nested) then
      remove_subsumed_mod_eq solved_rules
    else
      solved_rules
  in

  if check_inj_clauses id_thread restwork query lemmas initial_nb_premise solved_rules'
  then
    begin
      success_clauses := solved_rules' @ (!success_clauses);
      True
    end
  else
    display_attack solved_rules'

(* Main verification functions *)

let verify_inj_query id_thread display_when_true nested list_started all_lemmas (Before(evl,_) as query) =
  assert (!current_bound_vars == []);
  let request_rule = generate_initial_request_rule query in

  let initial_nb_premise = Query.number_of_facts_in_premise evl in

  let display_attack clauses =
    let tmp_faulty_clauses = !faulty_clauses_injective in
    faulty_clauses_injective := [];

    if tmp_faulty_clauses = []
    then
      begin
        (* The query is false due to the nested queries *)
        if is_non_nested_query query
        then Parsing_helper.internal_error __POS__ "[verify_inj_query] Should not happen since we already proved that the query is true without injectivity.";

        let clauses =
          (* Remove clauses subsumed modulo equational theory, when not already done,
             i.e. the query is nested. *)
          if !Param.simpeq_final && TermsEq.hasEquations() && nested then
            remove_subsumed_mod_eq clauses
          else
            clauses
        in
        let rec explore_clauses all_true = function
          | [] ->
              if all_true
              then Parsing_helper.internal_error __POS__ "[verify_inj_query] If all are true then it would imply that the query is false due to injectivity";
              DontKnow
          | cl::q_cl ->
              success_clauses := [];
              let sub_res = check_inj_clauses id_thread (fun () -> ()) query all_lemmas initial_nb_premise [cl] in
              success_clauses := [];
              if not sub_res
              then
                begin
                  if display_clause_trace id_thread all_lemmas true (Some (fun _ -> false)) (Some query) list_started cl
                  then False
                  else if (!traces_to_reconstruct != 0) && (!Param.reconstruct_derivation)
                  then explore_clauses false q_cl
                  else DontKnow
                 end
              else explore_clauses all_true q_cl
        in
        explore_clauses true  clauses
      end
    else
      let first_try = ref true in
      let res_att =
        List.exists (fun cl ->
          if !first_try
          then first_try := false
          else Display.Text.print_line "Trying to find a trace falsifying the query on another derivation.";

          (* I do not use recheck of the clause. It is not clear how I can check that
             a "double" clause does not satisfy the query. *)
          display_clause_trace id_thread all_lemmas true (Some (fun _ -> false)) (Some query) list_started cl
        ) tmp_faulty_clauses
      in

      if res_att
      then False
      else
        if List.length clauses = 1
        then DontKnow
        else
          begin
            (* We try with other clauses *)
            success_clauses := [];
            List.iter (fun cl -> ignore (check_inj_clauses id_thread (fun () -> ()) query all_lemmas initial_nb_premise [cl])) clauses;
            success_clauses := [];
            let res_att =
              List.exists (fun cl ->
                Display.Text.print_line "Trying to find a trace falsifying the query on another derivation.";

                (* I do not use recheck of the clause. It is not clear how I can check that
                   a "double" clause does not satisfy the query. *)
                display_clause_trace id_thread all_lemmas true (Some (fun _ -> false)) (Some query) list_started cl
              ) !faulty_clauses_injective
            in
            faulty_clauses_injective := [];
            if res_att
            then False
            else DontKnow
          end
  in

  success_clauses := [];
  let res = check_inj_query ~contain_nested:nested id_thread (fun () -> ()) display_attack all_lemmas initial_nb_premise request_rule query in
  let clauses = !success_clauses in
  success_clauses := [];
  if display_when_true && res = True then
    begin
      let clauses =
        (* Remove clauses subsumed modulo equational theory, when not already done,
           i.e. the query is nested. *)
        if !Param.simpeq_final && TermsEq.hasEquations() && nested then
          remove_subsumed_mod_eq clauses
        else
          clauses
      in
      if !Param.verbose_goal_reachable
      then  List.iter (fun cl -> ignore (display_clause_trace id_thread all_lemmas false None None list_started cl)) clauses
      else
        begin
          Display.Text.print_line ("Number of goals reachable: "^(string_of_int (List.length clauses)))
        end
    end;
  res

let verify_non_inj_query id_thread display_when_true nested list_started lemmas (Before(evl,_) as query) =
  assert (!current_bound_vars == []);
  let request_rule = generate_initial_request_rule query in

  let initial_nb_premise = Query.number_of_facts_in_premise evl in

  let display_attack cl =
    let recheck_fun cl =
      success_clauses := [];
      let res = check_non_inj_clauses id_thread None query lemmas initial_nb_premise [cl] in
      success_clauses := [];
      res = True
    in
    if display_clause_trace id_thread lemmas true (Some recheck_fun) (Some query) list_started cl
    then False
    else DontKnow
  in

  success_clauses := [];
  let res = check_query ~contain_nested:nested id_thread (Some display_attack) lemmas initial_nb_premise request_rule query in
  let clauses = !success_clauses in
  success_clauses := [];
  if display_when_true && res = True then
    begin
      let clauses =
        (* Remove clauses subsumed modulo equational theory, when not already done,
           i.e. the query is nested. *)
        if !Param.simpeq_final && TermsEq.hasEquations() && nested then
          remove_subsumed_mod_eq clauses
        else
          clauses
      in
      if !Param.verbose_goal_reachable
      then List.iter (fun cl -> ignore (display_clause_trace id_thread lemmas false None None list_started cl)) clauses
      else
        begin
          Display.Text.print_line ("Number of goals reachable: "^(string_of_int (List.length clauses)))
        end
    end;
  res

let verify_query id_thread display_query lemmas ind_lemmas qdisp (Before(el, _) as q) =
  Display.auto_cleanup_display (fun () ->
    Display.Text.print_string "Starting query ";
    Display.Text.display_corresp_secret_putbegin_query qdisp;
    Display.Text.newline();
    if (!Param.html_output) && display_query
    then
      begin
        Display.Html.print_string "<LI><span class=\"query\">Query ";
        Display.Html.display_corresp_secret_putbegin_query qdisp;
        Display.Html.print_string "</span><br>\n"
      end
        );
  traces_to_reconstruct := !Param.reconstruct_trace;
  shown_stop := false;
  assert (!current_bound_vars == []);

  let list_started = ref false in
  let result =
    let q' = copy_query q in
    cleanup();

    (* Check whether the query is non-nested && non_injective *)
    let is_simple = is_simple_query q' in

    if is_simple
    then verify_non_inj_query id_thread true false list_started (lemmas@ind_lemmas) q'
    else
      begin
        (* We simplify the query *)
        let simple_q = simplify_query q' in
        let result_simple = verify_non_inj_query id_thread false false list_started (lemmas@ind_lemmas) simple_q in
        supplemental_info := [simple_q, result_simple];
        (* If the simplified query cannot be proved, then q cannot be proved either.
           If we could reconstruct a trace against the simplified query, then q is false *)
        if result_simple <> True
        then result_simple
        else
          (* Otherwise we check the query q' itself *)
          let all_lemmas = lemmas@ind_lemmas in
          if is_non_injective_query q'
          then
            (* The query [q'] is not simple and it is non-injective, so it is nested *)
            verify_non_inj_query id_thread true true list_started all_lemmas q'
          else
            if is_non_nested_query q'
            then verify_inj_query id_thread true false list_started all_lemmas q'
            else
              begin
                (* We look at the simplified non-nested but injective query first *)
                let non_nested_q = remove_nested q' in
                let result_non_nested = verify_inj_query id_thread false false list_started all_lemmas non_nested_q in
                match result_non_nested with
                  | True ->
                      supplemental_info := [non_nested_q, result_non_nested];
                      (* When the simplified non-nested query is true, look at the real query *)
                      verify_inj_query id_thread true true list_started all_lemmas q'
                  | DontKnow ->
                      supplemental_info := (non_nested_q, result_non_nested) :: !supplemental_info;
                      DontKnow
                  | False ->
                      supplemental_info := [non_nested_q, result_non_nested];
                      False
              end
      end
  in

  if (!Param.html_output) && (!list_started)
  then Display.Html.print_string "</UL>\n";

  result

(* Prove *)

let do_query ?(partial=false) id_thread display_query lemmas ind_lemmas result_solve_queries index
    (solve_status,((qorig,_) as qorig_e), ((qencoded,_) as qencoded_e)) =
  match qencoded with
  | PutBegin _ -> ()
  | RealQuery (Before(el, concl_q) as q, []) ->
      (* We cleanup the existing proofs on ordering*)
      Ordering.cleanup_proved_ordering qencoded;

      faulty_clauses_injective := [];
      let r =
        if !for_biprocess && Rules.bad_in_saturated_database ()
        then DontKnow
        else verify_query id_thread display_query lemmas ind_lemmas qorig q
      in
      Display.Text.display_result_and_supplemental ~partial qorig qencoded r (!supplemental_info);
      if !Param.html_output
      then Display.Html.display_result_and_supplemental ~partial qorig qencoded r (!supplemental_info);

      supplemental_info := [];

      let r_query =
        if qorig != qencoded
        then CorrespQEnc([qorig_e,qencoded_e],solve_status)
        else CorrespQuery([qorig_e],solve_status)
      in
      result_solve_queries := (r,r_query,index) :: !result_solve_queries
  | RealQuery _ | QSecret _ ->
      Parsing_helper.internal_error __POS__ "Query secret and queries with public variables should have been encoded before Piauth.do_query"

(* Main function *)

let display_final_result list_results =
  Display.Text.display_final_result list_results;
  if !Param.html_output then
    Display.Html.display_final_result list_results

let solve_auth ?(id_thread=0) horn_state pi_state =
  let result_solve_queries = ref [] in
  let (queries, max_subset, induction) = match pi_state.pi_process_query with
    | SingleProcessSingleQuery(p_desc, CorrespQuery (ql,solve_status)) ->
        for_biprocess := p_desc.bi_pro;
        List.map (fun q -> (solve_status,q,q)) ql, solve_status.max_subset, solve_status.induction
    | SingleProcessSingleQuery(p_desc, CorrespQEnc (qql,solve_status)) ->
        for_biprocess := p_desc.bi_pro;
        List.map (fun (qorig, qencoded) -> (solve_status,qorig,qencoded)) qql, solve_status.max_subset, solve_status.induction
    | _ ->
       Parsing_helper.internal_error __POS__ "Unexpected process-query in piauth.ml"
  in
  List.iter (fun (_,_, query) -> Lemma.verify_conditions_query query) queries;
  init_clauses :=
    begin match horn_state.h_clauses with
      | Given rl -> rl
      | ToGenerate(rl,_) -> rl
    end;
  clauses_for_preds_Phaseless := None;
  clauses_for_preds_Std := None;
  declared_axioms := pi_state.pi_original_axioms;
  Rules.corresp_initialize horn_state;
  Ordering.are_ordering_proofs_recorded := pi_state.pi_originally_lemma;

  if !for_biprocess
  then
    begin match Rules.bad_in_saturated_database_opt () with
      | None -> ()
      | Some cl ->
          Terms.auto_cleanup (fun () ->
            Display.auto_cleanup_display (fun () ->
              Display.Text.print_string "goal reachable: ";
              Clause.Ord.Text.display_abbrev cl;
              if !Param.html_output then
                begin
                  Display.Html.print_string "goal reachable: ";
                  Clause.Ord.Html.display_abbrev cl
                end;
              let deriv = History.build_history None cl in
              if !Param.reconstruct_trace != 0 && !Param.reconstruct_derivation then
              ignore(Reduction_bipro.do_reduction ~bad_reached_in_lemmas:true None pi_state.pi_original_axioms deriv)
            )
          )
    end;

  let (lemmas,inductive_lemmas) =
    List.fold_left (fun (acc_lem,acc_ind) lem ->
      if not lem.l_verif_app
      then (acc_lem,acc_ind)
      else
        if lem.l_induction = None
        then (lem::acc_lem,acc_ind)
        else (acc_lem,lem::acc_ind)
    ) ([],[]) horn_state.h_lemmas
  in
  
  if max_subset && induction && inductive_lemmas <> [] && List.length queries > 1
  then
    begin
      if !Param.html_output then Display.Html.print_string "<UL>\n";
      Display.Text.print_line "Starting proving a group of queries by induction.";
      let i_queries = List.mapi (fun i q -> (i,q)) queries in
      let rec verify_queries ind_lemmas verified_queries to_verify =
        List.iter (fun (i,q) -> do_query ~partial:true id_thread true lemmas ind_lemmas result_solve_queries i q) to_verify;

        (* We look for queries that are false and that were proven by induction *)
        let verify_again = ref false in
        let new_ind_lemmas =
          List.filter (fun lem -> match lem.l_induction with
            | None -> internal_error __POS__ "[solve_auth] Inductive lemmas should have a correspond index for a query"
            | Some i ->
                if List.exists (fun (r,_,j) -> i = j && r <> True) !result_solve_queries
                then (verify_again := true; false)
                else true
          ) ind_lemmas
        in
        if !verify_again
        then
          begin
            let new_to_verify = List.filter (fun (i,q) -> List.exists (fun (r,_,j) -> i = j && r <> False) !result_solve_queries) to_verify in
            let new_verified = List.filter (fun (r,_,_) -> r = False) !result_solve_queries in

            result_solve_queries := [];
            Display.Text.print_line "Some inductive lemmas could not be verified.";
            if new_to_verify <> []
            then Display.Text.print_line "Restarting verification of queries without these inductive lemmas.";
            verify_queries new_ind_lemmas (verified_queries@new_verified) new_to_verify
          end
        else verified_queries @ !result_solve_queries
      in

      let results = List.rev_map (fun (r,r_query,_) -> r,r_query) (verify_queries inductive_lemmas [] i_queries) in
      if !Param.html_output then Display.Html.print_string "</UL>\n";
      display_final_result results;
      results
    end
  else
    match queries with
      | [q] ->
          (* Since there is only one query, we do not need to display partial result. *)
          do_query id_thread false lemmas inductive_lemmas result_solve_queries 0 q;
          List.map (fun (r,r_query,_) -> r,r_query) !result_solve_queries
      | _ ->
          let partial = not max_subset && induction in

          if !Param.html_output then Display.Html.print_string "<UL>\n";
          List.iteri (do_query ~partial:partial id_thread true lemmas inductive_lemmas result_solve_queries) queries;
          if !Param.html_output then Display.Html.print_string "</UL>\n";

          let results = List.rev_map (fun (r,r_query,_) -> r,r_query) !result_solve_queries in
          let results' =
            if partial
            then
              begin
                let final_results =
                  if List.for_all (function True,_ -> true | _,_ -> false) results
                  then results
                  else List.map (function (True,q) -> (DontKnow,q) | r -> r) results
                in
                display_final_result final_results;
                final_results
              end
            else results
          in
          results'
