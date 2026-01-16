open Types
open Pitypes
open Reduction_helper
open Clause
open Utils
  
(****************************************
  Description of lemma applications
*****************************************)

(************************)
(* Generation of lemmas *)

(* Internally, a lemma is a correspondence query F1 && ... && Fn ==> \psi such that:
    - \psi does not contain any nested query nor injective event. 
    - facts in \psi may ordered with respect to facts of the premises.
    - Attacker facts should not be asked to be proved < than an attacker fact of the premise.
        --> ProVerif would never be able to prove such ordering.
        --> This is the case for all queries (not only lemmas), so this point is checked
            in [Encode_queries.encode_temporal_realquery_e], not in [valid_lemma].
    - If the lemma is for equivalence use, it should not require occurrence variables
      (because it will be translated using the predicate event2 which has no occurrence).

  In an input file, we will prevent syntactically nested queries or injective events. We 
  allow temporal variables. Note that a query with temporal variables will be encoded into
  a query with possibly nested queries and ordered facts. Hence, only lemmas that can 
  be encoded into a valid internal lemma will be accepted.

  These conditions are verified in the function [valid_lemma].

  For queries that must be proved by induction, we generate a inductive lemma as follows:
    1) Injective events are replaced by normal events
    2) Encode the query with potentially temporal variables into a query with nested queries
       and ordered facts.
    3) We replace nested queries with conjunctions of facts
*)

(* Invariant of an element [lem] of type [lemma]. In the following, we refer as "blocking predicate" 
  a predicate p that is the result of the function [Terms.get_blocking_predicate]. We refer as 
  "unblocking predicate" a predicate that is the result of the function [Terms.unblock_predicate].
  As such, a user-defined predicate that is defined with the option [block] is both blocking and 
  unblocking. 

  1) Predicates of facts in [lem.l_premise] should only be unblocking. This includes event.
  2) Predicates of facts in [lem.l_conclusion] should only be blocking.
  3) [lem.l_nb_std_fact] indicates the number of standard facts in the premise of the lemma 
  4) [lem.l_nb_user_fact] indicates the number of user-defined facts in the premise of the lemma 
  5) When [lem.l_induction <> None] then the lemma is an inductive lemma. The integer refers to the query 
    index from the group this induction lemma refers to.
  6) Variables in [lem.l_constra] should all be contained in [lem.l_premise]
  7) Order of the facts in [lem.l_premise] should follow invariants of standard query, i.e. : standard 
    facts first and then user-defined facts
  8) Events in premise and conclusion of the lemma should follow the begin status given by 
    [Pievent.get_event_status].
*)

module Debug = 
struct
  
  let check_lemma lem = 
    (* Checking predicates in l_premise *)
    List.iter (function
      | Pred({ p_info = Block p;_},_)  ->
          Parsing_helper.debug_msg "Predicates in the premise of a lemma should only be unblocking.";
          Parsing_helper.debug_msg (Printf.sprintf "Blocking version of %s was found in the premise of lemma %d" p.p_name lem.l_index);
          Parsing_helper.internal_error __POS__ "check_lemma (1)"
      | _ -> ()
    ) lem.l_premise;
    
    (* Checking predications in l_conclusion *)
    List.iter (fun (factl,_,_) ->
      List.iter (fun (fact,_) -> match fact with
        | Pred({ p_info = Block p;_},_)  -> ()
        | Pred(p,_) when p.p_prop land Param.pred_BLOCKING != 0 -> ()
        | Pred(p,_) ->
            Parsing_helper.debug_msg "Predicates in the conclusion of a lemma should only be blocking.";
            Parsing_helper.debug_msg (Printf.sprintf "Predicate %s was found in the conclusion of lemma %d" p.p_name lem.l_index);
            Parsing_helper.internal_error __POS__ "check_lemma (2)"
      ) factl
    ) lem.l_conclusion;
    
    (* Checking the values of nb_std_fact, nb_user_fact *)
    let rec count_and_check = function
      | [] -> (0,0)
      | Pred(p,_) :: q ->
          let (nb_std,nb_user) = count_and_check q in
          if nb_std <> 0 && Terms.is_user_defined p
          then Parsing_helper.internal_error __POS__ "User defined predicates should not occur before standard predicates in the premise of a lemma.";
          
          match p.p_info with 
            | Subterm _ -> 
                if nb_std <> 0 || nb_user <> 0
                then Parsing_helper.internal_error __POS__ "Subterm predicates should not occur before standard or user-defined predicates in the premise of a lemma.";
                (0,0)
            | _ ->
                if Terms.is_user_defined p
                then (0,nb_user+1)
                else (nb_std+1,nb_user)
    in
    let (nb_std,nb_user) = count_and_check lem.l_premise in
    if nb_std <> lem.l_nb_std_fact
    then Parsing_helper.internal_error __POS__ (Printf.sprintf "Recorded number of standard fact in the premise of lemma %d does not match." lem.l_index);
    if nb_std <> lem.l_nb_std_fact
    then Parsing_helper.internal_error __POS__ (Printf.sprintf "Recorded number of user-defined fact in the premise of lemma %d does not match." lem.l_index);
    
    (* Checking the variables in constraints *)
    let premise_vars = ref [] in
    List.iter (Terms.get_vars_acc_fact premise_vars) lem.l_premise; 
    Terms.iter_constraints (Terms.iter_variables (fun v -> 
      if not (List.memq v !premise_vars)
      then Parsing_helper.internal_error __POS__ (Printf.sprintf "Variables in the constraint in the premise of lemma %d shall all be contained in the facts of the premise." lem.l_index);
    )) lem.l_constra;

    (* Checking begin status *)
    let check_event = function
      | Pred(p,FunApp(ev,_)::_) when (p == Param.event_pred || p == Param.event2_pred) && List.memq ev !Param.current_state.pi_precise_actions -> ()
      | Pred(p,FunApp(ev,_)::_) when Terms.is_event (Terms.unblock_predicate p) ->
          let status = Pievent.get_event_status !Param.current_state ev in
          begin match status.begin_status with
            | No -> Parsing_helper.internal_error __POS__ (Printf.sprintf "Events in lemma %d should have been recorded." lem.l_index)
            | NoOcc -> 
                if (Terms.unblock_predicate p) == Param.inj_event_pred
                then Parsing_helper.internal_error __POS__ (Printf.sprintf "Events in lemma %d with no occurrence recorded should not use the occ-event predicate." lem.l_index)
            | WithOcc ->
                if (Terms.unblock_predicate p) != Param.inj_event_pred
                then Parsing_helper.internal_error __POS__ (Printf.sprintf "Events in lemma %d with occurrence recorded should use the occ-event predicate." lem.l_index)
          end
      | _ -> ()
    in
    List.iter check_event lem.l_premise;
    List.iter (fun (factl,_,_) ->
      List.iter (fun (fact,_) -> check_event fact) factl
    ) lem.l_conclusion;

    (* Check that variables of the lemmas are not linked *)
    List.iter (Terms.iter_term_fact Terms.check_no_link) lem.l_premise;
    List.iter (fun (factl,constra,eqs) ->
      List.iter (fun (fact,_) ->
        Terms.iter_term_fact Terms.check_no_link fact
        ) factl;
      Terms.iter_constraints Terms.check_no_link constra;
      List.iter (fun (t1,t2) -> Terms.check_no_link t1; Terms.check_no_link t2) eqs
    ) lem.l_conclusion;
    List.iter (fun (t1,t2) -> Terms.check_no_link t1; Terms.check_no_link t2) lem.l_subterms

  (* Display functions *)

  let string_of_t_lemma_kind = function
  | Axiom -> "Axiom"
  | Lemma -> "Lemma"
  | Restriction -> "Restriction"

let display_disjunct (hypl,constra,eqs) =
  Display.Text.display_list (fun (fact,qrel) ->
    Display.Text.display_fact fact;
    print_string "{ ";
    Ordering.Debug.display_query_ordering_relation qrel;
    print_string " }"
  ) " && " hypl;

  if hypl <> [] && eqs <> []
  then print_string " && ";

  Display.Text.display_list (fun (t1,t2) ->
    Display.Text.display_term t1;
    print_string " = ";
    Display.Text.display_term t2
  ) " && " eqs;

  if not (Terms.is_true_constraints constra) && (eqs <> [] || hypl <> [])
  then print_string " && ";

  if not (Terms.is_true_constraints constra)
  then Display.Text.display_constraints constra

let display_lemma lem =
  Printf.printf "[DEBUG] - %s n°%d [sat_app=%b, verif_app=%b, nb_std_fact=%d, nb_user_fact=%d" 
    (string_of_t_lemma_kind lem.l_origin_kind) lem.l_index lem.l_sat_app lem.l_verif_app lem.l_nb_std_fact lem.l_nb_user_fact;

  begin match lem.l_induction with
    | None -> ()
    | Some i -> Printf.printf ", induction=%d" i
  end;
  print_string "]: ";
  Display.auto_cleanup_display (fun () ->
    Display.Text.display_list Display.Text.display_fact " && " lem.l_premise;
    if lem.l_subterms <> []
    then 
      begin 
        print_string " && ";
        Display.Text.display_list (fun (t1,t2) -> 
          Display.Text.display_term t1;
          print_string " in st(";
          Display.Text.display_term t2;
          print_string ")"
         ) " && " lem.l_subterms
      end;
    if not (Terms.is_true_constraints lem.l_constra)
    then 
      begin 
        print_string " && ";
        Display.Text.display_constraints lem.l_constra
      end;
    print_string " ==> ";
    begin match lem.l_conclusion with
      | [] -> print_string "false"
      | [concl] -> display_disjunct concl
      | _ -> 
        print_string "\n";
        Display.Text.display_list (fun concl ->
          print_string "[DEBUG]     ";
          display_disjunct concl
        ) " ||\n" lem.l_conclusion
    end;
    print_string "\n"
  )

let display_t_lemmas = function
  | LemmaToTranslate _ -> print_string "Lemma not translated\n"
  | Lemma lem_state ->
      List.iter (fun one_lem ->
        print_string "\n-- Original lemma: ";
        begin match one_lem.ql_original_query with
          | None -> print_string "none"
          | Some (q,_) -> Query.Debug.display_query q
        end;
        print_string "\nEncoded query: ";
        Query.Debug.display_query (fst one_lem.ql_query);
        print_string "\n"
      ) lem_state.lemmas
end

(****************************************
               Valid lemmas 
*****************************************)

let rec valid_concl ext is_equiv = function
  | QTrue | QFalse | QConstraints _ -> ()    
  | NestedQuery _ -> Parsing_helper.input_error "A lemma cannot contain nested queries or constraints on temporal variables that would be encoded in a nested query.\nThis usually happens when comparing the temporal variables of two facts in the conclusion of the lemma." ext
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) ->
      valid_concl ext is_equiv concl1;
      valid_concl ext is_equiv concl2
  | QEvent ev ->
      match ev with
        | QSEvent(Some _,_,_,_) -> Parsing_helper.input_error "A lemma cannot contain injective events." ext
        | QSEvent(_,_,Some _,_) when is_equiv -> Parsing_helper.input_error "A lemma used for equivalence queries should not require occurrence variables." ext
        | _ -> ()

let valid_lemma is_equiv lemma = match lemma.ql_query with
  | RealQuery(Before(prem,concl),[]), ext -> 
      valid_concl ext is_equiv concl
  | _ -> Parsing_helper.internal_error __POS__ "[valid_lemma] All lemmas should be correspondence query without public variables at that point."    

(****************************************
  Organize lemmas 
*****************************************)

(* The function [organize_lemmas pi_st] records which lemmas correspond to an axiom or restriction.
    It also removes lemmas that are not applied due to application options.
*)

exception Useless_lemma

let organize_lemmas pi_state =
  let original_axioms = ref [] in

  let rec simplify_lemma_state = function
    | [] -> []
    | (LemmaToTranslate _) :: _ -> Parsing_helper.internal_error __POS__ "Lemmas should have been translated at that point."
    | (Lemma lem_state)::q ->
        if lem_state.is_axiom = KAxiom || lem_state.is_axiom = KRestriction
        then
          original_axioms :=
            List.fold_left (fun acc lem -> match lem.ql_query with
              | RealQuery(rq,[]),ext -> ((rq,ext),lem_state.is_axiom = KAxiom)::acc
              | _ -> Parsing_helper.internal_error __POS__ "Lemmas should have been encoded at that point."
            ) !original_axioms lem_state.lemmas;

        if not (lem_state.solve_status.verif_app || lem_state.solve_status.sat_app)
        then simplify_lemma_state q
        else (Lemma lem_state) :: (simplify_lemma_state q)
  in
  let simplified_lemmas = simplify_lemma_state pi_state.pi_lemma in

  { pi_state with
    pi_lemma = simplified_lemmas;
    pi_original_axioms = !original_axioms
  }

(* The function [generate_inductive_lemmas pi_st] considers the query
   of [pi_st] and simplifies it to see if it can be proved by induction.

   The function [Piauth.simplify_query] must provide a stronger query
   than the simplified queries produced using
   [Lemma.generate_inductive_lemmas], because the proof of the query
   obtained by [Piauth.simplify_query] allows us to apply the
   inductive lemma.
   In particular, we simplify nested queries [e ==> concl] into conjunctions
   [e && concl] in both functions.

   Since queries are incompatible with equivalence, when
   [generate_inductive_lemmas] is called and we prove an equivalence,
   it is in fact called on a valid lemma so it changes nothing. (In
   particular, this function never needs to remove an occurrence
   because that is needed for equivalence only, and [valid_lemma]
   checks that no occurrence is used.) *)

(* In the generation of the inductive lemmas, we already indicate that the target order has been proved *)

let simplify_induction_ordering_data ord_data = 
  assert(ord_data.temp_var = None);
  assert(!(ord_data.ord_proved) = None);
  { ord_data with ord_proved = ref None }

let simplify_induction_event = function
  | QSEvent(_,ord_data,occ,ev) -> QSEvent(None,simplify_induction_ordering_data ord_data,occ,ev)
  | QSEvent2(ord_data,t1,t2) -> QSEvent2(simplify_induction_ordering_data ord_data,t1,t2)
  | QFact(p,ord_data,args) -> QFact(p,simplify_induction_ordering_data ord_data,args)
  | ev -> ev

let rec simplify_induction_conclusion_query = function
  | QEvent(ev) -> QEvent(simplify_induction_event ev)
  | NestedQuery(Before([e],concl)) ->
      simplify_induction_conclusion_query (QAnd(QEvent e, concl))
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[simplify_induction_conclusion_query] Nested queries should have exactly one premise."
  | QAnd(concl1,concl2) ->
      let concl1' = simplify_induction_conclusion_query concl1
      and concl2' = simplify_induction_conclusion_query concl2 in
      make_qand concl1' concl2'
  | QOr(concl1,concl2) ->
      let concl1' = simplify_induction_conclusion_query concl1
      and concl2' = simplify_induction_conclusion_query concl2 in
      make_qor concl1' concl2'
  | qev -> qev

let allowed_pred = function
  | QSEvent _ | QSEvent2 _ -> true
  | QFact(p,_,_) ->
      begin match p.p_info with
        | Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _ | UserPred _ -> true
        | _ -> false
      end
  | QNeq _ | QGeq _ | QIsNat _ -> true
  | QEq _ | QGr _ | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "[vars_and_allowed_pred] Equalities, strict inequalities, and max inequalities between time variables should not occur in the premise of the query."

let generate_inductive_lemmas pi_state =
  let (_,q) = Param.get_process_query pi_state in

  let analyze q_l solve_status =
    let sat_app =
      (* When we want to prove all queries, or when there is a single
         query, we can apply it as induction hypothesis in the saturation *)
      if solve_status.max_subset && List.length q_l > 1
      then false
      else solve_status.sat_app
    in

    if (not sat_app && not solve_status.verif_app) || not solve_status.induction
    then pi_state
    else
      let (simplified_queries,_) =
        List.fold_left (fun (acc,i) -> function
          | (RealQuery(Before(evl,concl),[]), ext) ->
              if List.for_all allowed_pred evl
              then
                let simp_concl = simplify_induction_conclusion_query concl in
		let simp_evl = List.map simplify_induction_event evl in
                Ordering.assume_proved_realquery (Before(simp_evl,simp_concl));
                if simp_concl <> QTrue
                then ({ ql_query = (RealQuery(Before(simp_evl,simp_concl),[]),ext) ;
			ql_original_query = None;
			ql_real_or_random = None;
			ql_index_query_for_induction = Some i;
			ql_application_side = AllSide }::acc,i+1)
                else (acc,i+1)
              else (acc,i+1)
          | _ -> (acc,i+1)
        ) ([],0) q_l
      in

      if simplified_queries = []
      then pi_state
      else
        let lem_state =
          {
            lemmas = simplified_queries;
            is_axiom = KLemma;
            keep_axiom = false;
            remove_events = RENone;
            solve_status = { solve_status with sat_app = sat_app }
          }
        in
        { pi_state with pi_lemma = (Lemma lem_state)::pi_state.pi_lemma}
  in

  match q with
    | CorrespQuery(q_l,solve_status) -> analyze q_l solve_status
    | CorrespQEnc(qql,solve_status) -> analyze (List.map (fun (_,q) -> q) qql) solve_status
    | NonInterfQuery _
    | WeakSecret _
    | ChoiceQuery | ChoiceQEnc _ -> pi_state
    | _ -> Parsing_helper.internal_error __POS__ "[simplify_queries_for_induction] Queries should have been translated"

(****************************************************
  Detection of a lemma with choice for monoprocess
*****************************************************)

(* [convert_lemma_for_monoprocess lem] checks whether the bilemma corresponds in fact to
   a lemma on one side of the biprocess. If it is the case, it returns the lemma for the
   corresponding side of the biprocess (ql_application_side is set to LeftSide or RightSide).
   When it is not the case, [lem] is returned.

   Note that technically, a lemma could correspond to both sides of the biprocess.
    ex : lemma event(A(x,y)) ==> event(B(x',y'))
   But in this case, it is sufficient to prove only one side of the lemma. In the case
   the lemma would be proved on one side but not on the other, it means that the biprocess
   diverges before the premises are triggered and so the lemma would not help anyway in the
   proof of equivalence. *)
let convert_lemma_for_monoprocess lemma =

  let explore_one_side left_side evl concl_q =
    let vars_side_to_keep = ref [] in
    let vars_side_to_check = ref [] in

    let add_variables vars =
      (* We check that terms in side_to_check are just distinct variables *)
      List.iter (function
        | Var v ->
            if List.memq v !vars_side_to_check || List.memq v !vars_side_to_keep
            then raise Not_found;
            vars_side_to_check := v :: !vars_side_to_check
        | _ -> raise Not_found
      ) vars
    in

    let rec check_keep_variables = function
      | Var v ->
          if List.memq v !vars_side_to_check
          then raise Not_found;

          if not (List.memq v !vars_side_to_keep)
          then vars_side_to_keep := v :: !vars_side_to_keep
      | FunApp(_,args) -> List.iter check_keep_variables args
    in

    let analyse_events = function
      | QSEvent2(ord_data,FunApp(f1,args1),FunApp(f2,args2)) ->
          assert (f1 == f2);
          let (side_to_check,side_to_keep) =  if left_side then (args2,args1) else (args1,args2) in
          add_variables side_to_check;
          List.iter check_keep_variables side_to_keep;
          QSEvent(None,ord_data,None,FunApp(f1,side_to_keep))
      | QSEvent2 _ -> Parsing_helper.internal_error __POS__ "[is_for_monoprocess] Argument of events should be a function application"
      | QFact(pred,ord_fun,args) ->
          let (new_pred,side_to_check, side_to_keep) = match pred.p_info, args with
            | AttackerBin(n,ty), [t1;t2] ->
                let (side_to_check,side_to_keep) = if left_side then ([t2],[t1]) else ([t1],[t2]) in
                Param.get_pred (Attacker(n,ty)), side_to_check, side_to_keep
            | MessBin(n,ty), [tc1;t1;tc2;t2] ->
                let (side_to_check,side_to_keep) = if left_side then ([tc2;t2],[tc1;t1]) else ([tc1;t1],[tc2;t2]) in
                Param.get_pred (Mess(n,ty)), side_to_check, side_to_keep
            | TableBin n, [FunApp(tbl1,args1);FunApp(tbl2,args2)] ->
                let (side_to_check,side_to_keep) = if left_side then (args2,[FunApp(tbl1,args1)]) else (args1,[FunApp(tbl2,args2)]) in
                Param.get_pred (Table n), side_to_check, side_to_keep
            | Attacker _, _
            | Mess _, _
            | Table _, _
            | Subterm _, _ -> pred, [], args
            | _ , _ -> Parsing_helper.internal_error __POS__ "[is_for_monoprocess] User defined predicates are not allowed for equivalence queries."
          in

          add_variables side_to_check;
          List.iter check_keep_variables side_to_keep;
          QFact(new_pred,ord_fun,side_to_keep)
      | (QNeq((t1,_),(t2,_)) | QEq((t1,_),(t2,_)) | QGeq((t1,_),(t2,_))) as p ->
          check_keep_variables t1;
          check_keep_variables t2;
          p
      | QIsNat t as p ->
          check_keep_variables t;
          p
      | QGr _ -> Parsing_helper.internal_error __POS__ "[is_for_monoprocess] Should not have temporal comparison at this point."
      | QSEvent _ -> Parsing_helper.internal_error __POS__ "[is_for_monoprocess] Event should have been translated into bievents at that point."
      | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "[is_for_monoprocess]  Max query should not occur here."
    in

    let rec analyse_concl = function
      | QTrue -> QTrue
      | QFalse -> QFalse
      | QConstraints constr -> Terms.iter_constraints check_keep_variables constr; QConstraints constr
      | QEvent ev -> QEvent (analyse_events ev)
      | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[is_for_monoprocess] Lemmas should not contain nested queries."
      | QAnd(concl1,concl2) -> QAnd(analyse_concl concl1, analyse_concl concl2)
      | QOr(concl1,concl2) -> QOr(analyse_concl concl1, analyse_concl concl2)
    in

    RealQuery(Before(List.map analyse_events evl, analyse_concl concl_q),[])
  in

  match lemma.ql_query with
    | (RealQuery(Before(evl,concl_q),_),ext) ->
        (* We try the left side *)
        begin
          try
            let rq = explore_one_side true evl concl_q in
            { lemma with ql_application_side = LeftSide; ql_query = (rq,ext) }
          with Not_found ->
            (* We try the right side *)
            try
              let rq = explore_one_side false evl concl_q in
              { lemma with ql_application_side = RightSide; ql_query = (rq,ext) }
            with Not_found -> lemma
        end
    | _ -> Parsing_helper.internal_error __POS__ "[is_for_monoprocess] Lemmas should only be correspondence queries."

(****************************************
  Translate to bi-lemmas
*****************************************)

(* [encode_event_equiv qev] transforms the query event [qev] into a fact for
   biprocess. Note that we do not allow disequalities, inequalities and equalities
   to contain choice. Moreover, since we do not allow user defined predicates for
   equivalence proofs, only Attacker, Mess and Table can have choice. Finally,
   user defined predicates are always considered as true when used for equivalence proofs. *)
let encode_event_equiv min_choice_phase next_f = function
  | QSEvent(_,ord_data,_,ev) ->
      let ev1 = Terms.choice_in_term 1 ev
      and ev2 = Terms.choice_in_term 2 ev in
      next_f (QSEvent2(ord_data,ev1,ev2))
  | QSEvent2 _ -> Parsing_helper.internal_error __POS__ "[encode_event_equiv] Event for biprocess should not occur before encoding."
  | QFact({p_info = Subterm _; _},_,_) as pred -> next_f pred
  | QFact(pred,ord_data,args) ->
      let n, bin_pred_spec =
        match pred.p_info with
        | Attacker(n,ty) -> n, AttackerBin(n,ty)
        | Mess(n,ty) -> n, MessBin(n,ty)
        | Table n -> n, TableBin n
        | _ -> raise Useless_lemma
      in
      let l1 = List.map (Terms.choice_in_term 1) args
      and l2 = List.map (Terms.choice_in_term 2) args in
      if n < min_choice_phase then
        TermsEq.unify_modulo_list (fun () -> next_f (QFact(pred,ord_data,l1))) l1 l2
      else
        next_f (QFact(Param.get_pred bin_pred_spec,ord_data, l1 @ l2))
  | (QNeq((t1,_),(t2,_)) | QGeq((t1,_),(t2,_))) as ev0 ->
      if Terms.has_choice t1 || Terms.has_choice t2
      then Parsing_helper.internal_error __POS__ "Disequalities and inequalities in queries should not contain choice.";
      next_f ev0
  | (QIsNat t) as ev0 ->
      if Terms.has_choice t
      then Parsing_helper.internal_error __POS__ "Predicates is_nat in queries should not contain choice.";
      next_f ev0
  | QEq _ | QGr _ | QMax _ | QMaxq _ ->
      Parsing_helper.internal_error __POS__ "[encode_event_equiv] equalities, strict inequalities and max inequalities between time variables cannot occur before ==> in queries"

let rec encode_event_equiv_list min_choice_phase next_f = function
    [] -> next_f []
  | a::l ->
      encode_event_equiv min_choice_phase (fun a' ->
        encode_event_equiv_list min_choice_phase (fun l' -> next_f (a'::l')) l
          ) a

let rec encode_conclusion_query min_choice_phase = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints q as constr -> 
    if Terms.exists_constraints Terms.has_choice q 
      then Parsing_helper.internal_error __POS__ "Constraints should not contain choice.";
    constr
  | (QEvent e) as ev0 ->
      begin
        match e with
        | QSEvent(_,ord_data,occ,ev) ->
            assert(occ = None);
            let ev1 = Terms.choice_in_term 1 ev
            and ev2 = Terms.choice_in_term 2 ev in
            QEvent(QSEvent2(ord_data,ev1,ev2))
        | QNeq((t1,_),(t2,_)) | QEq((t1,_),(t2,_)) | QGeq((t1,_),(t2,_)) ->
            if Terms.has_choice t1 || Terms.has_choice t2
            then Parsing_helper.internal_error __POS__ "Disequalities, inequalities and equalities in queries should not contain choice.";
            ev0
        | QIsNat t ->
            if Terms.has_choice t
            then Parsing_helper.internal_error __POS__ "Predicates is_nat in queries should not contain choice.";
            ev0
        | QFact(pred,ord_data,args) ->
            begin
              try
                let n, bin_pred_spec = match pred.p_info with
                  | Attacker(n,ty) -> n, AttackerBin(n,ty)
                  | Mess(n,ty) -> n, MessBin(n,ty)
                  | Table n -> n, TableBin n
                  | _ -> raise Useless_lemma
                in
                let l1 = List.map (Terms.choice_in_term 1) args
                and l2 = List.map (Terms.choice_in_term 2) args in
                if n < min_choice_phase then
                  let f_tuple = Terms.get_tuple_fun (List.map Terms.get_term_type l1) in
                  let eq_fact = QEq((FunApp(f_tuple,l1),Parsing_helper.dummy_ext),(FunApp(f_tuple,l2),Parsing_helper.dummy_ext)) in
                  let qfact = QFact(pred,ord_data,l1) in
                  QAnd(QEvent eq_fact,QEvent qfact)
                else
                  QEvent (QFact(Param.get_pred bin_pred_spec,ord_data, l1 @ l2))
              with Useless_lemma -> QTrue
            end
        | _ -> QTrue
      end
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[encode_conclusion_query] Lemmas should not contain nested queries."
  | QAnd(concl1,concl2) ->
      let concl1' = encode_conclusion_query min_choice_phase concl1
      and concl2' = encode_conclusion_query min_choice_phase concl2 in
      make_qand concl1' concl2'
  | QOr(concl1,concl2) ->
      let concl1' = encode_conclusion_query min_choice_phase concl1
      and concl2' = encode_conclusion_query min_choice_phase concl2 in
      make_qor concl1' concl2'

let translate_to_bi_lemma pi_state =
  match pi_state.pi_min_choice_phase with
  | Unset ->
      (* When pi_min_choice_phase is unset at this point, the process is not a biprocess *)
      if (Reduction_helper.get_process pi_state).bi_pro then
        Parsing_helper.internal_error __POS__ "[translate_to_bi_lemma] pi_min_choice_phase should be set";
      pi_state
  | Set min_choice_phase ->
      let new_lemmas =
        List.fold_left (fun acc1 -> function
          | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[translate_to_bi_lemma] Lemmas should have been translated."
          | Lemma lem_state ->
              let lemma_list =
                List.fold_left (fun acc2 lem -> match lem.ql_query with
                | (RealQuery(Before(evl,concl_q),pubvars),ext) ->
                    begin
                      let concl_q' = encode_conclusion_query min_choice_phase concl_q in
                      if concl_q' = QTrue then
                        acc2
                      else
                        let accu = ref acc2 in
                      (* Generate all lemmas with the various unification possibilities
                         for terms *)
                        try
                          Terms.auto_cleanup (fun () ->
                            encode_event_equiv_list min_choice_phase (fun evl' ->
                              accu :=
                                { lem with
				  ql_query = (RealQuery(Terms.copy_realquery2 (Before(evl',concl_q')),pubvars), ext);
				  ql_original_query =
				  match lem.ql_original_query with
				  | (Some _) as previous_original -> previous_original
				  | None -> Some(lem.ql_query) } :: (!accu);
                              raise Terms.Unify) evl
					     )
                        with
                        | Terms.Unify ->
                            if !accu == acc2 then
                              begin
                                let l0 = Parsing_helper.get_extent_string true ext in
                                Display.Text.print_string l0;
                                Display.Text.print_string "Warning: lemma ";
                                Display.Text.display_corresp_secret_putbegin_query (fst lem.ql_query);
                                Display.Text.print_string " ignored because it uses choice in phases without choice, and the two sides do not unify.\n";
                                if !Param.html_output then
                                  begin
                                    Display.Html.print_string l0;
                                    Display.Html.print_string "Warning: lemma ";
                                    Display.Html.display_corresp_secret_putbegin_query (fst lem.ql_query);
                                    Display.Html.print_string " ignored because it uses choice in phases without choice, and the two sides do not unify.\n"
                                  end;
                              end;
                            !accu
                        | Useless_lemma -> acc2
                    end
                | _ -> acc2
                      ) [] lem_state.lemmas
              in
              if lemma_list = []
              then acc1
              else (Lemma { lem_state with lemmas = List.rev lemma_list })::acc1
                                                                               ) [] pi_state.pi_lemma
      in
      { pi_state with pi_lemma = List.rev new_lemmas }

(****************************************
  Encode lemmas
*****************************************)

let encode_lemmas pi_state pubvars ror_opt =
  let new_lemmas =
    List.fold_left (fun acc1 -> function
      | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[encode_lemmas_for_correspondence] Lemmas should have been translated."
      | Lemma lem_state ->
          let lemma_list =
            List.fold_left (fun acc2 lem ->
              let same_ror = match ror_opt, lem.ql_real_or_random with
                | None, None -> true
                | Some vl, Some vl' -> Terms.same_term_lists vl vl'
                | _ -> false
              in
              if same_ror
              then
                begin match lem.ql_query with
                  | RealQuery(rq,pubvars'),ext when Terms.same_term_lists pubvars' pubvars ->
                      if pubvars = []
                      then lem::acc2
                      else { ql_query = (RealQuery(rq,[]), ext); ql_original_query = Some(lem.ql_query); ql_real_or_random = lem.ql_real_or_random; ql_index_query_for_induction = None; ql_application_side = AllSide } :: acc2
                  | _ ->
                      (* Lemmas that do not have the same public vars are ignored. *)
                      acc2
                end
              else
                (* Lemmas that do not correspond to the same query secret real_or_random are ignored. *)
                acc2
            ) [] lem_state.lemmas
          in
          if lemma_list = []
          then acc1
          else (Lemma { lem_state with lemmas = List.rev lemma_list })::acc1
    ) [] pi_state.pi_lemma
  in
  { pi_state with pi_lemma = List.rev new_lemmas }

let encode_lemmas_for_equivalence_queries pi_state =
  let new_lemmas =
    List.fold_left (fun acc1 -> function
      | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[encode_lemmas_for_correspondence] Lemmas should have been translated."
      | Lemma lem_state ->
          let lemma_list =
            List.filter (fun lem -> match lem.ql_query, lem.ql_real_or_random with
              | (RealQuery(_,[]),_), None -> true
              | _ -> false
            ) lem_state.lemmas
          in
          if lemma_list = []
          then acc1
          else (Lemma { lem_state with lemmas = lemma_list })::acc1
    ) [] pi_state.pi_lemma
  in
  { pi_state with pi_lemma = List.rev new_lemmas }

(*****************************************************
  Verification of conditions on lemmas and queries
******************************************************)

(* In a query 'F ==> H', F can contain function symbols
    that can be reduced by the equational theory only if 
    it does not introduce ambiguity in the conclusion.

    The query \psi ==> \phi must satisfy the following condition:
    if \rho is a fresh renaming of the variables of \psi
    then
      forall substitutions \sigma,
      \psi\sigma =_E \psi\rho\sigma implies \phi\sigma =_E \phi\rho\sigma
*)

let create_equations_premises_op_term acc = function
  | None -> ()
  | Some t -> acc := (t,Terms.copy_term t) :: !acc

let create_equations_premises_op_term_e acc = function
  | None -> ()
  | Some (t,_) -> acc := (t,Terms.copy_term t) :: !acc

let create_equations_premises acc = function
  | QSEvent(_,{ temp_var = x_t; _},occ,ev) ->
      acc := (ev,Terms.copy_term ev) :: !acc;
      create_equations_premises_op_term acc occ;
      create_equations_premises_op_term_e acc x_t
  | QSEvent2({ temp_var = x_t; _},t1,t2) ->
      acc := (t1,Terms.copy_term t1) :: (t2,Terms.copy_term t2) :: !acc;
      create_equations_premises_op_term_e acc x_t
  | QGeq ((t1,_),(t2,_)) | QNeq ((t1,_),(t2,_)) ->
      acc := (t1,Terms.copy_term t1) :: (t2,Terms.copy_term t2) :: !acc
  | QFact(_,{ temp_var = x_t; _},args) ->
      List.iter (fun t ->
        acc := (t,Terms.copy_term t) :: !acc 
      ) args;
      create_equations_premises_op_term_e acc x_t
  | QIsNat t ->
      acc := (t,Terms.copy_term t) :: !acc
  | _ -> Parsing_helper.internal_error __POS__ "[create_equations_premisses] Unexpected element in the premises of queries, lemmas and axioms."

let rec follow_vlink = function
  | Var {link = VLink v; _ } -> Var v
  | FunApp(f,args) -> FunApp(f,List.map follow_vlink args)
  | t -> t

let create_equations_concl_term acc t = acc := (t,follow_vlink t) :: !acc

let create_equations_concl_term_e acc (t,_) = create_equations_concl_term acc t

let create_equations_concl_op_term acc = function
  | None -> ()
  | Some t -> acc := (t,follow_vlink t) :: !acc

let create_equations_concl_op_term_e acc = function
  | None -> ()
  | Some (t,_) -> acc := (t,follow_vlink t) :: !acc

let create_equations_concl_event acc = function
  | QSEvent(_,{ temp_var = x_t; _},occ,ev) ->
      acc := (ev,follow_vlink ev) :: !acc;
      create_equations_concl_op_term acc occ;
      create_equations_concl_op_term_e acc x_t
  | QSEvent2({ temp_var = x_t; _},t1,t2) ->
      acc := (t1,follow_vlink t1) :: (t2,follow_vlink t2) :: !acc;
      create_equations_concl_op_term_e acc x_t
  | QFact(_,{ temp_var = x_t; _},args) ->
      List.iter (fun t ->
        acc := (t,follow_vlink t) :: !acc 
      ) args;
      create_equations_concl_op_term_e acc x_t
  | QNeq(t1,t2)
  | QEq(t1,t2)
  | QGeq(t1,t2)
  | QGr(t1,t2) ->
      create_equations_concl_term_e acc t1;
      create_equations_concl_term_e acc t2
  | QIsNat t -> acc := (t,follow_vlink t) :: !acc
  | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "[create_equations_concl_event] Max queries should not occur at that point."

let rec create_equations_concl acc = function
  | QTrue | QFalse -> ()
  | QConstraints q -> Terms.iter_constraints (create_equations_concl_term acc) q
  | QEvent ev -> create_equations_concl_event acc ev
  | NestedQuery (Before (evl,concl)) ->
      List.iter (create_equations_concl_event acc) evl;
      create_equations_concl acc concl
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) ->
      create_equations_concl acc concl1;
      create_equations_concl acc concl2

let rec put_constants2 = function
  | Var v ->
      begin match v.link with
        | TLink t -> put_constants2 t
        | NoLink ->
            v.link <- TLink (FunApp({ f_name = Renamable v.vname;
                                      f_type = [], v.btype;
                                      f_cat = SpecVar v;
                                      f_initial_cat = SpecVar v;
                                      f_private = false;
                                      f_options = 0;
                                      f_record = Param.fresh_record () }, []));
            Terms.current_bound_vars := v :: (!Terms.current_bound_vars)
        | _ -> Parsing_helper.internal_error __POS__ "[put_constants2] Unexpected link."
      end
  | FunApp(f,l) -> List.iter put_constants2 l

let verify_deterministic cat (query,ext) = match query with
  | PutBegin _ | QSecret _ -> ()
  | RealQuery (Before(el,concl),_) -> 
      let eqs_premise = ref [] in 
      let eqs_concl = ref [] in   

      Terms.auto_cleanup (fun () ->
        List.iter (create_equations_premises eqs_premise) el;
        create_equations_concl eqs_concl concl
      );

      let (l1,l2) = List.split !eqs_premise in
    
      try 
        TermsEq.unify_modulo_list (fun () ->
          begin 
            Terms.auto_cleanup (fun () ->
              List.iter (fun (t1,t2) ->
                put_constants2 t1;
                put_constants2 t2
                  ) !eqs_concl;
              List.iter (fun (t1,t2) ->
                try 
                  TermsEq.unify_modulo (fun () -> ()) t1 t2
                with Terms.Unify -> 
                  print_string (Parsing_helper.get_extent_string true ext);
                  print_string ("Error in the "^cat^": ");
                  Display.Text.display_corresp_secret_putbegin_query query;
                  print_string ".\nThe term ";
                  Display.Text.display_term t1; (* Does not follow links, so displays the original term in the query *)
                  print_string (" in the conclusion of this "^cat^" is not determined by the premise of this "^cat^": it can take different values for the same value of the premise, due to the equational theory.\n");
                  Parsing_helper.user_error "Incorrect query"
                ) !eqs_concl
              )
          end;
          (* We raise unify to try all unifiers of the premise. *)
          raise Terms.Unify
        ) l1 l2
      with Terms.Unify -> () 

let verify_conditions_query query =
  verify_deterministic "query" query

let verify_conditions_lemma lem_state =
  List.iter (fun lem ->
    verify_deterministic "lemma or axiom" lem.ql_query
      ) lem_state.lemmas

(****************************************
  Translation of lemmas for Horn clauses
*****************************************)

(* Copy functions *)

let copy_query = function
  | RealQuery(rq,[]),ext -> RealQuery(Terms.copy_realquery rq,[]),ext
  | _ -> Parsing_helper.internal_error __POS__ "[copy_query] Should be a real query without public vars"

let copy_lemma lemma = { lemma with ql_query = copy_query lemma.ql_query }

let copy_lemma_state lem_state = { lem_state with lemmas = List.map copy_lemma lem_state.lemmas }

(* Native axioms *)

let precise_action equiv ev_act id =
  let ty = match fst ev_act.f_type with
    | [_;ty] -> ty
    | _ -> Parsing_helper.internal_error __POS__ "[precise_action] Event precise action should only have two arguments."
  in

  if equiv
  then
    let occ = Var(Terms.new_var ~orig:false "occ" Param.occurrence_type)
    and x = Var(Terms.new_var ~orig:false "x" ty)
    and y = Var(Terms.new_var ~orig:false "y" ty)
    and x' = Var(Terms.new_var ~orig:false "x'" ty)
    and y' = Var(Terms.new_var ~orig:false "y'" ty) in

    let ev1 = Pred(Param.event2_pred,[FunApp(ev_act,[occ;x]);FunApp(ev_act,[occ;x'])])
    and ev2 = Pred(Param.event2_pred,[FunApp(ev_act,[occ;y]);FunApp(ev_act,[occ;y'])]) in

    {
      l_index = id;
      l_premise = [ev1;ev2];
      l_nb_std_fact = 2;
      l_nb_user_fact = 0;
      l_subterms = [];
      l_constra = Terms.true_constraints;
      l_conclusion = [([],Terms.true_constraints,[x,y; x',y'])];
      l_verif_app = true;
      l_sat_app = true;
      l_origin_kind = Axiom;
      l_induction = None;
      l_remove_events = RENone;
    }
  else
    let occ = Var(Terms.new_var ~orig:false "occ" Param.occurrence_type)
    and x = Var(Terms.new_var ~orig:false "x" ty)
    and y = Var(Terms.new_var ~orig:false "y" ty) in

    let ev1 = Pred(Param.event_pred,[FunApp(ev_act,[occ;x])])
    and ev2 = Pred(Param.event_pred,[FunApp(ev_act,[occ;y])]) in

    {
      l_index = id;
      l_premise = [ev1;ev2];
      l_nb_std_fact = 2;
      l_nb_user_fact = 0;
      l_subterms = [];
      l_constra = Terms.true_constraints;
      l_conclusion = [([],Terms.true_constraints,[x,y])];
      l_verif_app = true;
      l_sat_app = true;
      l_origin_kind = Axiom;
      l_induction = None;
      l_remove_events = RENone;
    }

(* Translating functions *)

let add_predicate_to_prove pred_to_prove p = 
  if not (List.memq p (!pred_to_prove)) then
    pred_to_prove := p :: (!pred_to_prove)

let add_predicate_to_prove_event pred_to_prove = function
  | QSEvent _ | QSEvent2 _ | QFact({p_info = Subterm _; _},_,_) -> ()
  | QFact(p,_,_) -> add_predicate_to_prove pred_to_prove p
  | _ -> ()

let rec add_predicate_to_prove_concl pred_to_prove = function
  | QTrue | QFalse | QConstraints _ -> ()
  | QEvent ev -> add_predicate_to_prove_event pred_to_prove ev
  | NestedQuery rq -> add_predicate_to_prove_realquery pred_to_prove rq
  | QOr(concl1,concl2)
  | QAnd(concl1,concl2) ->
      add_predicate_to_prove_concl pred_to_prove concl1;
      add_predicate_to_prove_concl pred_to_prove concl2

and add_predicate_to_prove_realquery pred_to_prove = function
  | Before(evl,concl) ->
      List.iter (add_predicate_to_prove_event pred_to_prove) evl;
      add_predicate_to_prove_concl pred_to_prove concl

(* The translation of a lemma will apply the blocking predicates on the conclusion
  of the query but will leave the premise of the lemma with non-blocking predicates
  (this includes events). We could have made a exception for events but it seems
  better for uniformity. 
*)

type transl_state_lemma =
  {
    l_facts : (fact * query_ordering_relation) list;
    l_constra : constraints;
  }

let transl_premise_event next_f pi_state = function
  | QSEvent(_,_,occ_op,(FunApp(f,_) as t)) -> 
      let fstatus = Pievent.get_event_status pi_state f in
      if fstatus.begin_status = WithOcc
      then
        let occ = match occ_op with
            | None -> Var(Terms.new_var ~orig:false "o" Param.occurrence_type)
            | Some occ -> occ (* It should also be a variable *)
        in
        TermsEq.close_term_eq (fun t1 -> 
          next_f (Pred(Param.inj_event_pred,[t1;occ]))
        ) t
      else
        TermsEq.close_term_eq (fun t1 ->
          next_f (Pred(Param.event_pred,[t1]))
        ) t
  | QSEvent2(_,t1,t2) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f (Pred(Param.event2_pred,[t1';t2']))
        ) t2
      ) t1
  | QFact(p,_,tl) ->
      TermsEq.close_term_list_eq (fun tl1 -> next_f (Pred(p,tl1))) tl
  | _ -> Parsing_helper.internal_error __POS__ "[transl_premise_event] Premise of a lemma should not contain equalities or disequalities"

let rec transl_premise next_f pi_state = function
  | [] -> next_f [] Terms.true_constraints
  | QNeq ((t1,_),(t2,_)) ::q ->
      transl_premise (fun q' constra' -> 
        next_f q' (Terms.wedge_constraints (Terms.constraints_of_neq t1 t2) constra')  
      ) pi_state q
  | QGeq ((t1,_),(t2,_)) ::q ->
      transl_premise (fun q' constra' -> 
        next_f q' (Terms.wedge_constraints (Terms.constraints_of_geq t1 t2) constra')  
      ) pi_state q
  | QIsNat t ::q ->
      transl_premise (fun q' constra' -> 
        next_f q' (Terms.wedge_constraints (Terms.constraints_of_is_nat t) constra')  
      ) pi_state q
  | ev::q ->
      transl_premise_event (fun fact ->
        transl_premise (fun q' constra' -> next_f (fact::q') constra'
        ) pi_state q
      ) pi_state ev

let get_proved_extended_ordering_function ord_data = match !(ord_data.ord_proved) with
  | Some eord_fun -> eord_fun
  | _ -> 
      Parsing_helper.internal_error __POS__ "[get_proved_extended_ordering_function] The lemma should be proved."

(* All events and facts are replaced by their blocking predicate counterpart in
  the conclusion of the lemma. *)
let rec transl_conclusion_query next_f pi_state cur_state = function
  | QConstraints q -> next_f { cur_state with l_constra = Terms.wedge_constraints q cur_state.l_constra }
  | QTrue -> next_f cur_state
  | QFalse -> ()
  | QEvent(QSEvent(_,ord_data,_,_) | QFact(_,ord_data,_)) when !(ord_data.ord_proved) = None -> ()
  | QEvent(QSEvent(_,ord_data,occ_op,(FunApp(f,_) as t))) ->
      let eord_fun = get_proved_extended_ordering_function ord_data in
      let fstatus = Pievent.get_event_status pi_state f in
      if fstatus.begin_status = WithOcc
      then
        let occ = match occ_op with
          | None -> Var(Terms.new_var ~orig:false "o" Param.occurrence_type)
          | Some occ -> occ
        in
        TermsEq.close_term_eq (fun t1 ->
          next_f { cur_state with l_facts = (Pred(Param.inj_event_pred_block,[t1;occ]),eord_fun) :: cur_state.l_facts }
        ) t
      else
        TermsEq.close_term_eq (fun t1 ->
          next_f { cur_state with l_facts = (Pred(Param.event_pred_block,[t1]),eord_fun) :: cur_state.l_facts }
        ) t
  | QEvent(QSEvent _) -> Parsing_helper.internal_error __POS__ "[transl_conclusion] Unexpected event"
  | QEvent(QSEvent2(ord_data,t1,t2)) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f { cur_state with l_facts = (Pred(Param.event2_pred_block,[t1';t2']),ord_data.ord_target) :: cur_state.l_facts }
        ) t2
      ) t1
  | QEvent(QFact(p,ord_data,args)) ->
      let eord_fun = get_proved_extended_ordering_function ord_data in
      TermsEq.close_term_list_eq (fun args1 ->
        let block_p = Terms.get_blocking_predicate p in
        next_f { cur_state with l_facts = (Pred(block_p,args1),eord_fun) :: cur_state.l_facts }
      ) args
  | QEvent(QNeq((t1,_),(t2,_))) -> next_f { cur_state with l_constra = { cur_state.l_constra with neq = [t1,t2] :: cur_state.l_constra.neq } }
  | QEvent(QGeq((t1,_),(t2,_))) ->
      assert(Terms.get_term_type t1 == Param.nat_type);
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f { cur_state with l_constra = { cur_state.l_constra with geq = (t1',0,t2') :: cur_state.l_constra.geq } }
        ) t2
      ) t1
  | QEvent(QGr _) -> Parsing_helper.internal_error __POS__ "[transl_conclusion] Lemma should not contain strict inequalities."
  | QEvent(QIsNat t) ->
      assert(Terms.get_term_type t == Param.nat_type);
      TermsEq.close_term_eq (fun t' ->
        next_f { cur_state with l_constra = { cur_state.l_constra with is_nat = t' :: cur_state.l_constra.is_nat } }
      ) t
  | QEvent(QEq((t1,_),(t2,_))) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          try
            Terms.auto_cleanup (fun () ->
              Terms.unify t1' t2';
              next_f cur_state
            )
          with Terms.Unify -> ()
        ) t2
      ) t1
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[transl_conclusion] Lemma should not have nested queries."
  | QAnd(concl1,concl2) ->
      transl_conclusion_query (fun cur_state1 ->
        transl_conclusion_query next_f pi_state cur_state1 concl2
      ) pi_state cur_state concl1
  | QOr(concl1,concl2) ->
      transl_conclusion_query next_f pi_state cur_state concl1;
      transl_conclusion_query next_f pi_state cur_state concl2
  | QEvent(QMax _) | QEvent(QMaxq _) -> Parsing_helper.internal_error __POS__ "[transl_conclusion_query] Max queries should not occur at that point."

let transl_realquery next_f pi_state = function
    [@ppwarning "Vincent: do a full simplification of lemmas in this function?"]
  | Before(ev_l,concl_q) ->
      transl_premise (fun premise constra_premise ->
        let premise = List.map Terms.copy_fact4 premise in
        let vars_premise = Terms.get_vars_fact_list premise in
        

        let concl_accu = ref [] in
        let cur_state_0 = { l_facts = []; l_constra = Terms.true_constraints } in

        try
          transl_conclusion_query (fun cur_state1 ->
            try
              (* Follow the links *)
              let constra1 = Terms.copy_constra4 cur_state1.l_constra in

              let vars_table_event_mess = 
                Terms.get_vars_generic4 (fun f fact_l -> 
                  List.iter (function 
                    | Pred(p,args) when Terms.is_event (Terms.unblock_predicate p) -> List.iter f args
                    | Pred({ p_info = Mess _ | MessBin _ | Table _ | TableBin _; _},args) -> List.iter f args
                    | _ -> ()
                  ) fact_l
                ) premise
              in

              let fact_list1 = List.map (fun (f,eord) -> Terms.copy_fact4 f,eord) cur_state1.l_facts in
              let fact_list2 = 
                List.filter_map (fun (Pred(p,args) as fact,eord) -> match eord with
                  | QONone -> Some(fact, QONone)
                  | QOMax(sem,ord) -> 
                      if not (Terms.is_attacker (Terms.unblock_predicate p)) && sem = SemPhaseLess 
                      then Parsing_helper.internal_error __POS__ "Only attacker predicate should have PhaseLess semantics at that stage.";
                      
                      if sem <> SemPhaseLess || (Terms.are_variable_included_fact2 vars_table_event_mess (Pred(p,args)))
                      then Some (fact,QOMax(sem,ord))
                      else None
                  | QOSpecific ord_l ->
                      let vars_included = Terms.are_variable_included_fact2 vars_table_event_mess (Pred(p,args)) in
                      let ord_l' = 
                        List.filter (fun (_,(sem,ord)) ->
                          if not (Terms.is_attacker (Terms.unblock_predicate p)) && sem = SemPhaseLess 
                          then Parsing_helper.internal_error __POS__ "Only attacker predicate should have PhaseLess semantics at that stage.";

                          sem <> SemPhaseLess || vars_included
                        ) ord_l
                      in
                      if ord_l' = [] then None else Some(fact,QOSpecific ord_l')

                ) fact_list1
              in

              let keep_vars = ref vars_premise in
              List.iter (fun (f,_) -> Terms.get_vars_acc_fact keep_vars f) fact_list2;
              List.iter (fun v -> match v.link with
                | TLink t -> Terms.get_vars_acc keep_vars (Terms.copy_term4 t)
                | _ -> ()
              ) vars_premise;

              let next_step constra =
                let eq_list1 =
                  List.fold_left (fun acc v ->
                    match v.link with
                      | NoLink -> acc
                      | TLink t -> (Var v,Terms.copy_term4 t)::acc
                      | _ -> Parsing_helper.internal_error __POS__ "[transl_realquery] Unexpected link."
                  ) [] vars_premise
                in

                (* Removing simple equations *)

                Terms.auto_cleanup (fun () ->
                  let eq_list2 =
                    List.fold_left (fun acc (t1,t2) -> match t2 with
                      | Var v when v.link = NoLink && not (List.memq v vars_premise) ->
                          Terms.link v (TLink t1);
                          acc
                      | _ -> (t1,t2)::acc
                    ) [] eq_list1
                  in

                  let eq_list3 = List.map (fun (t1,t2) -> t1, Terms.copy_term3 t2) eq_list2 in
                  let constra3 = Terms.copy_constra3 constra in
                  let fact_list3 = List.map (fun (f,eord) -> Terms.copy_fact3 f, eord) fact_list2 in

                  if eq_list3 = [] && Terms.is_true_constraints constra3 && fact_list3 = []
                  then
                    (* The conclusion is true so the we can discard this lemma as it is of the
                      form F_1 && ... && F_n ==> true || \phi *)
                    raise Useless_lemma;

                  concl_accu := (fact_list3,constra3,eq_list3) :: !concl_accu
                )
              in
              let get_vars_op = Some (fun () -> !keep_vars) in
              TermsEq.simplify_constraints_continuation get_vars_op next_step next_step constra1
            with Terms.Unify | TermsEq.FalseConstraint -> ()
          ) pi_state cur_state_0 concl_q;
          next_f premise constra_premise !concl_accu
        with Useless_lemma -> ()
      ) pi_state ev_l

let rec transl_lemmas horn_state pi_state =
  let h_lemmas = ref [] in
  let pred_prove = ref horn_state.h_pred_prove in
  let nb_lemmas = ref 0 in
  let equiv = (horn_state.h_solver_kind = Solve_Equivalence || horn_state.h_solver_kind = Solve_CorrespBipro) in

  (* Adding the native precise actions *)
  List.iter (fun ev ->
    let lemma = precise_action equiv ev !nb_lemmas in
    incr nb_lemmas;
    h_lemmas := lemma :: !h_lemmas
  ) pi_state.pi_precise_actions;

  List.iter (function
    | Lemma lem_state ->
        let lem_state' = Terms.auto_cleanup (fun _ -> copy_lemma_state lem_state ) in
        (* Check that the lemmas does not contain destructor. Moreover, we also check that the
           function symbols of the premises are not reduced by the equational theory. *)
        verify_conditions_lemma lem_state';

        let kind = match lem_state.is_axiom with
          | KAxiom -> Types.Axiom
          | KLemma -> Types.Lemma
          | KRestriction -> Types.Restriction
        in

        let sat_app = lem_state.solve_status.sat_app in
        let verif_app = lem_state.solve_status.verif_app in

        List.iter (fun lem -> match lem.ql_query with
        | RealQuery(rq,[]),_ ->
            (* Add predicates to [pred_prove]
               The predicates in assumptions of lemmas must be added
               to [pred_prove] because, when we apply a lemma,
               we must be sure that the predicate is actually true.
               Therefore, we must not resolve on this predicate in
               elimination of redundant clauses, to avoid removing
               a clause that does not have this predicate in hypothesis.

               Queries proved by induction are already included in lemmas
               at this stage, so we do not need to handle them separately. *)
            add_predicate_to_prove_realquery pred_prove rq;

            let (nb_std,nb_user) = Query.count_std_and_user_facts rq in 

            transl_realquery (fun premise constra_premise concl ->
              let (subterm_facts,other_facts) = List.partition (function Pred({p_info = Subterm _;_},_) -> true | _ -> false) premise in
              let subterms =
                List.map (function
                  | Pred(_,[t1;t2]) -> (t1,t2)
                  | _ -> Parsing_helper.internal_error __POS__ "[transl_lemmas] Unexpected number of arguments."
                ) subterm_facts
              in
              
              let lemma =
                {
                  l_index = !nb_lemmas;
                  l_premise = other_facts;
                  l_nb_std_fact = nb_std;
                  l_nb_user_fact = nb_user;
                  l_subterms = subterms;
                  l_constra = constra_premise;
                  l_conclusion = concl;
                  l_verif_app = verif_app;
                  l_sat_app = sat_app;
                  l_origin_kind = kind;
                  l_induction = lem.ql_index_query_for_induction;
                  l_remove_events = lem_state.remove_events;
                }
              in
              incr nb_lemmas;
              h_lemmas := lemma :: !h_lemmas
            ) pi_state rq
          | _ -> Parsing_helper.internal_error __POS__ "[transl_lemmas] Unexpected query"
        ) lem_state.lemmas
    | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[transl_lemmas_for_correspondence] Lemma should be translated at this point."
  ) pi_state.pi_lemma;

  { horn_state with
    h_lemmas = List.rev !h_lemmas;
    h_pred_prove = !pred_prove }

(************************************************
  Verification of axioms on reconstructed trace
*************************************************)

let continue_searching ev state =
  match ev with
  | QFact({ p_info = Mess(n,_) | MessBin(n,_) | Table(n) | TableBin(n); _},_,_)
      when state.current_phase < n -> false
  | QEq _ | QNeq _ | QGeq _ | QIsNat _ -> false
  | _ -> true

let unify_hyp f_next ev state = match ev with
  (* attacker can occur only the premise of axioms and restrictions.
   When it occurs, we should look for terms that the attacker can compute
   and prove the axiom/restriction for all these terms.
   That's too complicated, so we exclude this case below and just do
   not verify such axioms/restrictions.
  | QFact({ p_info = [Attacker(n,_)]; _},_,[tq],_) when state.current_phase <= n->
      begin match state.comment with
        | RInput_Success(_,_,_,_,t)
        | ROutput_Success(_,_,_,t)
            (* RIO/RIO_PatRemove send on a public channel only when the adversary
               is passive. When the channel is public, the recipe is set to "Some ..." *)
        | RIO(_,_,_,_,_,Some _,t,_)
        | RIO_PatRemove(_,_,_,_,_,Some _,t,_,_) ->
            (* In case we work with biprocesses, in a phase < min_choice_phase,
               we may have a fact Attacker and still a biterm in the trace. *)
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq;t2] [t1;t1]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = [AttackerBin(n,_)]; _},_,[tq1;tq2],_) when state.current_phase <= n->
      begin match state.comment with
        | RInput_Success(_,_,_,_,t)
        | ROutput_Success(_,_,_,t)
            (* RIO/RIO_PatRemove send on a public channel only when the adversary
               is passive. When the channel is public, the recipe is set to "Some ..." *)
        | RIO(_,_,_,_,_,Some _,t,_)
        | RIO_PatRemove(_,_,_,_,_,Some _,t,_,_) ->
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq1;tq2] [t1;t2]
        | _ -> raise Terms.Unify
      end
        *)
  | QFact({ p_info = Mess(n,_); _},_,[c;tq]) when state.current_phase = n ->
      begin match state.comment with
        | RInput_Success(_,tc,_,_,t)
        | ROutput_Success(_,tc,_,t)
        | RIO(_,tc,_,_,_,_,t,_)
        | RIO_PatRemove(_,tc,_,_,_,_,t,_,_) ->
            (* In case we work with biprocesses, in a phase < min_choice_phase,
               we may have a fact Mess and still biterms in the trace. *)
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            let tc1 = Terms.choice_in_term 1 tc in
            let tc2 = Terms.choice_in_term 2 tc in
            TermsEq.unify_modulo_list f_next [c;tc2;tq;t2] [tc1;tc1;t1;t1]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = MessBin(n,_); _},_,[c1;tq1;c2;tq2]) when state.current_phase = n ->
      begin match state.comment with
        | RInput_Success(_,tc,_,_,t)
        | ROutput_Success(_,tc,_,t)
        | RIO(_,tc,_,_,_,_,t,_)
        | RIO_PatRemove(_,tc,_,_,_,_,t,_,_) ->
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            let tc1 = Terms.choice_in_term 1 tc in
            let tc2 = Terms.choice_in_term 2 tc in
            TermsEq.unify_modulo_list f_next [c1;c2;tq1;tq2] [tc1;tc2;t1;t2]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = Table(n); _},_,[tq]) when state.current_phase = n ->
      begin match state.comment with
        | RInsert_Success(_,t,_) ->
            (* In case we work with biprocesses, in a phase < min_choice_phase,
               we may have a fact Table and still a biterm in the trace. *)
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [t1;t1] [tq;t2]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = TableBin(n); _},_,[tq1;tq2]) when state.current_phase = n ->
      begin match state.comment with
        | RInsert_Success(_,t,_) ->
            let t1 = Terms.choice_in_term 1 t in
            let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq1;tq2] [t1;t2]
        | _ -> raise Terms.Unify
      end
  | QFact(p,_,args) when p.p_prop land Param.pred_BLOCKING != 0 ->
      (* The trace satisfies the blocking predicate in question,
         but we can not sure that the trace actually exists
         (because it depends on the real semantics of the blocking predicate).
         ProVerif will say "cannot be proved" anyway for this reason. *)
      begin match state.comment with
        | RLetFilter_In(_,[],[],Pred(p',args')) when p == p' -> TermsEq.unify_modulo_list f_next args args'
        | _ -> raise Terms.Unify
      end
  | QSEvent(_,_,_,ev') ->
      begin match state.comment with
        | REvent_Success(_,ev'',_) -> TermsEq.unify_modulo f_next ev' ev''
        | _ -> raise Terms.Unify
      end
  | QSEvent2(_,ev1,ev2) ->
      begin match state.comment with
        | REvent_Success(_,ev'',_) ->
            let ev1'' = Terms.choice_in_term 1 ev'' in
            let ev2'' = Terms.choice_in_term 2 ev'' in
            TermsEq.unify_modulo_list f_next [ev1;ev2] [ev1'';ev2'']
        | _ -> raise Terms.Unify
      end
  | QEq((t1,_),(t2,_)) -> TermsEq.unify_modulo f_next t1 t2
        (* Constraints QNeq, QGeq, QIs_nat are collected in [match_conclusion] and
           proved in [check_one_axiom], so we need not verify them here. *)
  | _ -> raise Terms.Unify

(* Event in match conclusion should be ground (no variables) *)
let rec match_conclusion restwork state ev =
  try
    unify_hyp restwork ev state
  with Terms.Unify ->
    if continue_searching ev state
    then
      match state.previous_state with
        | None -> raise Terms.Unify
        | Some state' -> match_conclusion restwork state' ev
    else raise Terms.Unify

let rec match_conclusion_query restwork state constra = function
  | QTrue -> restwork constra
  | QFalse -> raise Terms.Unify
  | QConstraints q -> restwork (Terms.wedge_constraints q constra)
  | QEvent (QNeq((t1,_),(t2,_))) ->
      restwork { constra with neq = [t1,t2]::constra.neq }
  | QEvent (QGeq((t1,_),(t2,_))) ->
      TermsEq.close_term_eq_synt (fun t1' ->
        TermsEq.close_term_eq_synt (fun t2' ->
          restwork { constra with geq = (t1',0,t2)::constra.geq }
        ) t2
      ) t1
  | QEvent (QIsNat t) ->
      TermsEq.close_term_eq_synt (fun t' ->
        restwork { constra with is_nat = t'::constra.is_nat }
      ) t
  | QEvent ev ->
      match_conclusion (fun () -> restwork constra) state ev
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[match_conclusion_query] Axioms should not contain nested correspondence"
  | QAnd(concl1,concl2) ->
      match_conclusion_query (fun constra1 ->
        match_conclusion_query restwork state constra1 concl2
      ) state constra concl1
  | QOr(concl1,concl2) ->
      try
        match_conclusion_query restwork state constra concl1
      with Terms.Unify ->
        match_conclusion_query restwork state constra concl2

let rec match_one_premise f_next state ev =
  try
    unify_hyp f_next ev state;
    raise Terms.Unify
  with Terms.Unify ->
    if continue_searching ev state
    then
      match state.previous_state with
        | None -> ()
        | Some state' -> match_one_premise f_next state' ev

let rec not_ground = function
  | Var { link = TLink t } -> not_ground t
  | Var _ -> true
  | FunApp(_,args) -> List.exists not_ground args

exception AxiomNotVerified

let rec cannot_be_verified_conclusion_query = function
  | QTrue | QFalse | QConstraints _ (* constraints can always be verified *)
  | QEvent(QNeq _ | QEq _ | QGeq _ | QIsNat _ | QSEvent _ | QSEvent2 _) -> false
  | QEvent(QFact({ p_info = UserPred _; _} as p,_,_)) when p.p_prop land Param.pred_BLOCKING != 0 -> false
  | QEvent(QFact({ p_info = Mess _ | MessBin _ | Table _ | TableBin _; _},_,_)) -> false
  | QEvent(QFact({ p_info = Attacker _ | AttackerBin _ | UserPred _ ; _},_,_)) -> true
  | QEvent(QFact _) -> Parsing_helper.internal_error __POS__ "[cannot_be_verified_conclusion_query] Axioms and restrictions should only contain attacker, mess, table facts, events, user-defined predicates, inequalities, disequalities and equalities in their conclusion"
  | QEvent(QGr _) -> Parsing_helper.internal_error __POS__ "[cannot_be_verified_conclusion_query] Axioms and restrictions should not contain time inequalities."
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) ->
      cannot_be_verified_conclusion_query concl1 ||
      cannot_be_verified_conclusion_query concl2
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[cannot_be_verified_conclusion_query] A lemma should not contain nested queries."
  | QEvent(QMax _) | QEvent(QMaxq _) -> Parsing_helper.internal_error __POS__ "[cannot_be_verified_conclusion_query] Max queries should not occur at that point."

let cannot_be_verified_premise = function
  | QFact({ p_info = Subterm _ | Attacker _ | AttackerBin _ | UserPred _ ; _},_,_) -> true
  | QFact({ p_info = Mess _ | MessBin _ | Table _ | TableBin _; _},_,_) -> false
  | QNeq _ | QGeq _ | QIsNat _ -> false
  | QSEvent _ | QSEvent2 _ -> false
  | QFact _ | QEq _ | QGr _ | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "axioms and restrictions should only contain subterm, attacker, mess, table facts, events, user-defined predicates, disequalities, inequalities between natural numbers, or is_nat in their premise"

let cannot_be_verified = function
  | Before(evl,concl_q) as ax ->
      Reduction_helper.has_name_q ax ||
      List.exists cannot_be_verified_premise evl ||
      cannot_be_verified_conclusion_query concl_q

let check_one_axiom final_state is_axiom = function
  | Before(evl,concl_q) as ax, ext ->
      let str_axiom = if is_axiom then "axiom" else "restriction" in
      let display_warning () =
        Display.Text.newline();
        begin
          match Parsing_helper.get_extent true ext with
          | None ->
              Display.Text.print_line ("Warning: We could not verify that the following "^str_axiom^" is satisfied by the attack trace.");
          | Some s ->
              Display.Text.print_line ("Warning: We could not verify that the following "^str_axiom^", declared at "^s^", is satisfied by the attack trace.")
        end;
        Display.Text.display_corresp_query (Before(evl,concl_q));
        Display.Text.newline();
      in

      let rec match_premises constra_prem state = function
        | [] -> 
            (* Premise have been matched excepted the constraints *)
            let constra_prem1 = Terms.map_constraints TermsEq.remove_syntactic_term constra_prem in
            if not (TermsEq.check_closed_constraints constra_prem1)
            then raise Terms.Unify;

            (* All premise have been matched *)
            let exists_existential_vars = ref false in

            begin
            try
              match_conclusion_query (fun constra ->
                try
                  let constra1 = Terms.map_constraints TermsEq.remove_syntactic_term constra in
                  let constra2 =
                    TermsEq.simplify_constraints_continuation (Some (fun () -> [])) (fun c -> c) (fun _ ->
                      Parsing_helper.internal_error __POS__ "[check_one_axiom] Should not occur since we have kept no variables."
                    ) constra1
                  in
                  TermsEq.check_constraints constra2;

                  (* When there are still natural number in the constra, we cannot
                      correctly verify that the axiom is not verified by the trace.
                      In such a case, we will display a warning saying that we could not verify
                      the axiom *)

                  if Terms.exists_constraints not_ground constra2
                  then
                    begin
                      exists_existential_vars := true;
                      raise Terms.Unify
                    end;
                with TermsEq.FalseConstraint -> raise Terms.Unify
              ) state Terms.true_constraints concl_q;
            with Terms.Unify ->
              if !exists_existential_vars
              then
                begin
                  display_warning ();
                  if not is_axiom then raise AxiomNotVerified
                end
              else
                begin
                  Display.Text.newline();
                  begin
                    match Parsing_helper.get_extent true ext with
                    | None ->
                        Display.Text.print_line ("The attack trace does not satisfy the following declared "^str_axiom^":")
                    | Some s ->
                        Display.Text.print_line ("The attack trace does not satisfy the following "^str_axiom^", declared at "^s^":")
                  end;
                  Display.Text.display_corresp_query (Before(evl,concl_q));
                  Display.Text.newline();
                  raise AxiomNotVerified
                end
            end
        | QNeq ((t1,_),(t2,_))::q_ev ->
            match_premises (Terms.wedge_constraints (Terms.constraints_of_neq t1 t2) constra_prem) state q_ev
        | QGeq ((t1,_),(t2,_))::q_ev ->
            match_premises (Terms.wedge_constraints (Terms.constraints_of_geq t1 t2) constra_prem) state q_ev
        | QIsNat t :: q_ev ->
            match_premises (Terms.wedge_constraints (Terms.constraints_of_is_nat t) constra_prem) state q_ev
        | ev::q_ev ->
            match_one_premise (fun () ->
              match_premises constra_prem state q_ev
            ) state ev

      and match_state state prev_ev = function
        | [] ->
            begin match state.previous_state with
              | None -> ()
              | Some state' -> match_state state' [] evl
            end
        | ev::q_ev ->
            try
              unify_hyp (fun () -> match_premises Terms.true_constraints state (prev_ev @ q_ev)) ev state;
              raise Terms.Unify
            with Terms.Unify -> match_state state (ev::prev_ev) q_ev
      in

      try
        if cannot_be_verified ax
        then
          begin
            (* When an axiom contains a subterm fact or some bound names, we assume that it is verified. However, if it is
               a restriction, we assume that it is false.
               TODO : Improve the verification when there is no equational theory for subterms
               Similarly, when an axiom or restriction contains attacker(..) as premise, it is
               hard to verify, because we must prove that it is true for all values that the
               attacker can compute. We leave that for the future. *)
            display_warning ();
            is_axiom
          end
        else
          begin
            match_state final_state [] evl;
            true
          end
      with AxiomNotVerified ->
        false

let check_axioms final_state axioms =
  (* First check restrictions *)
  let restrictions_ok = List.for_all (fun (rq,is_axiom) ->
    if not is_axiom then check_one_axiom final_state is_axiom rq else true
      ) axioms
  in
  (* Check axioms if restrictions are ok.
     By checking axioms only if the restrictions are satisfied,
     we allow the user to specify axioms that are valid only
     on the traces that satisfy the restrictions. *)
  if restrictions_ok then
    List.iter (fun (rq,is_axiom) ->
      if is_axiom then
        if not (check_one_axiom final_state is_axiom rq) then
          Parsing_helper.user_error "False axiom."
            ) axioms;
  restrictions_ok

(************************************************
   Verification that lemmas do not contain PGLink
 *************************************************)

let rec no_bound_name_term = function
  | Var { link = PGLink _ } -> false
  | Var { link = TLink t } -> no_bound_name_term t
  | Var _ -> true
  | FunApp(_,args) -> List.for_all no_bound_name_term args

let no_bound_name_term_option = function
  | None -> true
  | Some t -> no_bound_name_term t

let no_bound_name_term_e_option = function
  | None -> true
  | Some (t,_) -> no_bound_name_term t

let no_bound_name_event = function
  | QSEvent(_,_,occ,t) -> no_bound_name_term_option occ && no_bound_name_term t
  | QIsNat t -> no_bound_name_term t
  | QFact(_,_,args) -> List.for_all no_bound_name_term args
  | QNeq((t1,_),(t2,_))
  | QEq((t1,_),(t2,_))
  | QGeq((t1,_),(t2,_))
  | QSEvent2(_,t1,t2) -> no_bound_name_term t1 && no_bound_name_term t2
  | QGr _ -> Parsing_helper.internal_error __POS__ "[no_bound_name_event] Lemma should not contain strict disequalities."
  | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "[no_bound_name_event] Max queries should not occur at that point."

let rec no_bound_name_conclusion_query = function
  | QTrue
  | QFalse -> true
  | QConstraints q -> Terms.forall_constraints no_bound_name_term q
  | QEvent ev -> no_bound_name_event ev
  | NestedQuery r -> no_bound_name_realquery r
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> no_bound_name_conclusion_query concl1 && no_bound_name_conclusion_query concl2

and no_bound_name_realquery = function
  | Before(evl,concl) ->
      List.for_all no_bound_name_event evl &&
      no_bound_name_conclusion_query concl

let no_bound_name_query = function
  | RealQuery(q,_),_ -> no_bound_name_realquery q
  | _ -> Parsing_helper.internal_error __POS__ "[no_bound_name_query] Unexpected query."

let no_bound_name_t_lemmas = function
  | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[no_bound_name_t_lemmas] Lemma should be translated at that point."
  | Lemma lem_st -> List.for_all (fun lem -> no_bound_name_query lem.ql_query) lem_st.lemmas
