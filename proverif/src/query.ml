open Types
open Pitypes

let rec count_std_and_user_facts_event = function
  | [] 
  | QFact({ p_info = Subterm _;_},_,_)::_ -> (0,0)
  | QFact({ p_info = UserPred _; _ },_,_) :: q ->
      let (nb_std,nb_user) = count_std_and_user_facts_event q in
      if nb_std <> 0
      then Parsing_helper.internal_error __POS__ "[query.count_std_and_user_facts_event] Wrong order. A standard fact appear after a user defined one.";
      (0,nb_user+1)
  | (QFact _ | QSEvent _ | QSEvent2 _)::q ->
      let (nb_std,nb_user) = count_std_and_user_facts_event q in
      (nb_std+1,nb_user)
  | _ -> (0,0)

let count_std_and_user_facts = function
  | Before(evl,_) -> count_std_and_user_facts_event evl

(* Tools *)

let map_term_event f = function
  | QSEvent(b,ord_data,occ,t) ->
      assert(ord_data.temp_var = None);
      let occ' =
	match occ with
	| None -> None
	| Some o -> Some (f o)
      in
      QSEvent(b,ord_data,occ',f t)
  | QSEvent2(ord_data,t1,t2) -> 
      assert(ord_data.temp_var = None);
      QSEvent2(ord_data,f t1,f t2)
  | QFact(p,ord_data,tl) ->
      assert(ord_data.temp_var = None);
      QFact(p,ord_data,List.map f tl)
  | QNeq((t1,e1),(t2,e2)) -> QNeq((f t1,e1), (f t1,e2))
  | QGeq((t1,e1),(t2,e2)) -> QGeq((f t1,e1), (f t1,e2))
  | QEq((t1,e1),(t2,e2)) -> QEq((f t1,e1), (f t1,e2))
  | QIsNat t -> QIsNat(f t)
  | QGr _ -> Parsing_helper.internal_error __POS__ "[query.map_term_event] Queries with strict temporal inequalities should have been encoded by now."
  | QMax _ | QMaxq _ -> Parsing_helper.internal_error __POS__ "[query.specvar_to_var_event] Queries with max inequalities should have been encoded by now."

let rec map_term_realquery f = function
  | Before(el,concl_q) -> Before(List.map (map_term_event f) el, map_term_conclusion_query f concl_q)

and map_term_conclusion_query f = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QConstraints q -> QConstraints(Terms.map_constraints f q)
  | QEvent e -> QEvent(map_term_event f e)
  | NestedQuery q -> NestedQuery (map_term_realquery f q)
  | QAnd(concl1,concl2) -> QAnd(map_term_conclusion_query f concl1, map_term_conclusion_query f concl2)
  | QOr(concl1,concl2) -> QOr(map_term_conclusion_query f concl1, map_term_conclusion_query f concl2)


(* Get the number of premises, constraints and subterm excluded *)

let rec number_of_facts_in_premise = function
  | [] -> 0
  | (QNeq _ | QGeq _ | QIsNat _) :: q_ev 
  | QFact({ p_info = Subterm _; _},_,_) :: q_ev -> number_of_facts_in_premise q_ev
  | (QSEvent _ | QSEvent2 _ | QFact _):: q_ev -> 1 + number_of_facts_in_premise q_ev
  | (QMax _  | QMaxq _ | QEq _ | QGr _ )::_ -> 
      Parsing_helper.internal_error __POS__ "[Query.number_of_facts_in_premise] After encoding, premise of a query should not contain =, > and max."


(* Debugging *)

module Debug =
struct
  let display_event = function
    | QSEvent(inj_op,ord_data,occ_op,ev) ->
        begin match inj_op with
          | Some i -> Printf.printf "inj-%d-" i
          | None -> ()
        end;
        print_string "event(";
        Display.Text.display_term ev;
        begin match occ_op with
          | Some occ -> print_string ","; Display.Text.display_term occ
          | None -> ()
        end;
        print_string ")";
        Ordering.Debug.display_ordering_data ord_data
    | QSEvent2(ord_data,ev1,ev2) ->
        print_string "bievent(";
        Display.Text.display_term ev1;
        print_string ",";
        Display.Text.display_term ev2;
        print_string ")";
        Ordering.Debug.display_ordering_data ord_data
    | QFact(p,ord_data,args) ->
        Display.Text.display_fact (Pred(p,args));
        Ordering.Debug.display_ordering_data ord_data
    | QNeq((t1,_),(t2,_)) ->
        Display.Text.display_term t1;
        print_string " <> ";
        Display.Text.display_term t2
    | QEq((t1,_),(t2,_)) ->
        Display.Text.display_term t1;
        print_string " = ";
        Display.Text.display_term t2
    | QGeq((t1,_),(t2,_)) ->
        Display.Text.display_term t1;
        print_string " ≥ ";
        Display.Text.display_term t2
    | QGr((t1,_),(t2,_)) ->
        Display.Text.display_term t1;
        print_string " > ";
        Display.Text.display_term t2
    | QIsNat t ->
        print_string "is_nat(";
        Display.Text.display_term t;
        print_string ")"
    | QMax(t,args) ->
        Display.Text.display_term t;
        print_string " < max(";
        Display.Text.display_list Display.Text.display_term "," args;
        print_string ")"
    | QMaxq(t,args) ->
        Display.Text.display_term t;
        print_string " ≤ max(";
        Display.Text.display_list Display.Text.display_term "," args;
        print_string ")"  
        
  let is_or = function
    | QOr _ -> true
    | _ -> false

  let is_and = function
    | QAnd _ -> true
    | _ -> false

  let rec display_conclusion_query = function
    | QTrue -> print_string "top"
    | QFalse -> print_string "bot"
    | QConstraints q -> Display.Text.display_constraints q
    | QEvent ev -> display_event ev
    | NestedQuery rq ->
        print_string "(";
        display_realquery rq;
        print_string ")"
    | QAnd(concl1,concl2) ->
        if is_or concl1 then print_string "(";
        display_conclusion_query concl1;
        if is_or concl1 then print_string ")";
        print_string " && ";
        if is_or concl2 then print_string "(";
        display_conclusion_query concl2;
        if is_or concl2 then print_string ")"
    | QOr(concl1,concl2) ->
        if is_and concl1 then print_string "(";
        display_conclusion_query concl1;
        if is_and concl1 then print_string ")";
        print_string " || ";
        if is_and concl2 then print_string "(";
        display_conclusion_query concl2;
        if is_and concl2 then print_string ")"

  and display_realquery = function
    | Before(ev,concl) ->
        Display.Text.display_list display_event " && " ev;
        print_string " ==> ";
        display_conclusion_query concl

  let display_query = function
    | PutBegin _ -> print_string "PutBegin"
    | QSecret _ -> print_string "QSecret"
    | RealQuery(rq,vars) ->
        Display.auto_cleanup_display (fun () ->
          print_string "RealQuery";
          if vars <> []
          then 
            begin
              print_string "(pub_vars: ";
              Display.Text.display_list Display.Text.display_term "," vars;
              print_string ")"
            end;
          print_string ": ";
          display_realquery rq
        )

  let display_t_query = function
    | CorrespQuery(ql,_) ->
        Display.Text.display_item_list ~tab:true (fun (q,_) ->
          print_string "Query: ";
          display_query q
        ) ql
    | CorrespQEnc(qencl,_) ->
        Display.Text.display_item_list ~tab:true (fun ((q,_),(q_orig,_)) ->
          print_string "Query: ";
          display_query q_orig;
          print_string "\n";
          print_string "Query encoded: ";
          display_query q
        ) qencl
    | _ -> print_string "Other queries"

end
