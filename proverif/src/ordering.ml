open Types
open Pitypes
open Terms
open Utils

[@ppwarning "Vincent: ordering. It may be better to say that all user-defined predicates are before protocol steps
e.g. by using the lexicographic ordering on
   - (0, length of derivation) for user-defined predicates
   - (1, step in the trace) for protocol steps.
(It may not be for this version; as you prefer.)"]

(** Display debugging functions *)

module Debug = 
struct

  let display_clause_order = function
    | Less -> print_string "<"
    | Leq -> print_string "≤"

  let display_query_order = function
    | SemIO, Less -> print_string "<_{IO}"
    | SemIO, Leq -> print_string "≤_{IO}"
    | SemPhaseLess, Less -> print_string "<_p"
    | SemPhaseLess, Leq -> print_string "≤_p"
    | SemStd, Less -> print_string "<_i"
    | SemStd, Leq -> print_string "≤_i"

  let display_query_ordering_relation = function
    | QONone -> print_string "∅"
    | QOMax ord -> 
        print_string "max(";
        display_query_order ord;
        print_string ")"
    | QOSpecific ord_l ->
        Display.Text.display_list (fun (i,ord) -> 
          display_query_order ord;
          print_string " ";
          print_int i  
        ) ", " ord_l

  let display_clause_ordering_relation = function
    | CONone -> print_string "∅"
    | COMax ord -> 
        print_string "max(";
        display_clause_order ord;
        print_string ")"
    | COSpecific ord_l ->
        Display.Text.display_list (fun (i,ord) -> 
          display_clause_order ord;
          print_string " ";
          print_int i  
        ) ", " ord_l

  let display_ordering_data ord_data =
    print_string "{ target = ";
    display_query_ordering_relation ord_data.ord_target;
    begin match !(ord_data.ord_proved) with
      | None -> ()
      | Some ord_rel -> 
          print_string "; proved = ";
          display_query_ordering_relation ord_rel
    end;
    begin match ord_data.temp_var with
      | None -> ()
      | Some (t,_) -> 
          print_string "; temp_var = ";
          Display.Text.display_term t
    end;
    print_string "}"  
end 

(** Predicates to prove *)

type predicates_to_prove_t =
  {
    mutable tp_attacker : int; (* The maximal phase for the attacker predicate *)
    mutable tp_table : int; (* The maximal phase for the table predicate *)
    mutable tp_others : predicate list
  }

(* For attacker facts that occur in the conclusion of queries, we need
   to add all attacker facts of previous phases and of any type to the predicates to prove.
   For attacker facts that occur in hypotheses of lemmas, we need to add
   all attacker facts of previous phases to predicates to prove
   (because the lemma matching allows matching attacker phase n in the hypothesis of the clause
   with attacker phase n' for n'>=n in the hypothesis of the lemma).
   For simplicity, in both cases, we add all attacker facts of previous phases and of any type
   to the predicates to prove, and we remember only the maximum phase in field [tp_attacker].
*)

let pred_to_prove = { tp_attacker = -1; tp_table = -1; tp_others = [] }

let initialise_pred_to_prove pred_list =
  pred_to_prove.tp_attacker <- -1;
  pred_to_prove.tp_table <- -1;
  pred_to_prove.tp_others <- [];

  List.iter (fun p -> match p.p_info with
    | Attacker(n,_) | AttackerBin(n,_) -> pred_to_prove.tp_attacker <- max pred_to_prove.tp_attacker n
    | Table n | TableBin n -> pred_to_prove.tp_table <- max pred_to_prove.tp_table n
    | _ ->
        if not (List.memq p pred_to_prove.tp_others)
        then pred_to_prove.tp_others <- p :: pred_to_prove.tp_others
  ) pred_list

let reset_pred_to_prove () =
  pred_to_prove.tp_attacker <- -1;
  pred_to_prove.tp_table <- -1;
  pred_to_prove.tp_others <- []

let is_pred_to_prove p = match p.p_info with
  | Attacker(n,_) | AttackerBin(n,_) -> pred_to_prove.tp_attacker >= n
  | Table n | TableBin n -> pred_to_prove.tp_table >= n
  | _ ->
      p == Param.event_pred_block || p == Param.inj_event_pred_block || p == Param.event2_pred_block ||
      p == Param.event_pred || p == Param.inj_event_pred || p == Param.event2_pred ||
      List.memq p pred_to_prove.tp_others

let is_pred_to_prove_fact = function
  | Pred(p,_) -> is_pred_to_prove p

(** Inclusion functions *)

let rec includes_clause_order_list ord_l1 ord_l2 = match ord_l1, ord_l2 with
  | [], _ -> true
  | _, [] -> false
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> false
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> includes_clause_order_list ord_l1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (_,Less)::q1, (_,Leq)::q2 -> false
  | _::q1, _::q2 -> includes_clause_order_list q1 q2

(** [includes_clause ord1 ord2] return [true] only if [R(ord2) \subseteq R(ord1)]. *)
let includes_clause ord_fun1 ord_fun2 = match ord_fun1, ord_fun2 with
  | CONone, _ -> true
  | _, CONone -> false
  | COMax ord1, COMax ord2 -> ord1 <> Less || ord2 <> Leq
  | COMax Leq, _ -> true
  | COMax Less, COSpecific ord_l2 -> List.exists (fun (_,ord2) -> ord2 = Less) ord_l2
  | _, COMax _ -> false
  | COSpecific ord_l1, COSpecific ord_l2 -> includes_clause_order_list ord_l1 ord_l2

(** Inclusion between query relations *)

let includes_query_order ((sem1,ord1):query_order) ((sem2,ord2):query_order) = 
  (ord1 <> Less || ord2 = Less) &&
  (match sem1,sem2 with
  | SemStd, _ 
  | SemPhaseLess , (SemIO | SemPhaseLess) -> true
  | _ -> false 
  )

let rec includes_query_order_list ord_l1 ord_l2 = match ord_l1, ord_l2 with
  | [], _ -> true
  | _, [] -> false
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> false
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> includes_query_order_list ord_l1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (_,ord1)::q1, (_,ord2)::q2 -> 
      if includes_query_order ord1 ord2
      then includes_query_order_list q1 q2  
      else false

let includes_query rel1 rel2 = match rel1, rel2 with
  | QONone, _ -> true
  | _, QONone -> false
  | QOMax ord1, QOMax ord2 -> includes_query_order ord1 ord2
  | QOMax ord1, QOSpecific ord_l2 -> List.exists (fun (_,ord2) -> includes_query_order ord1 ord2) ord_l2
  | _, QOMax _ -> false
  | QOSpecific ord_l1, QOSpecific ord_l2 -> includes_query_order_list ord_l1 ord_l2

let rec includes_query_clause_order_list ord_l1 ord_l2 = match ord_l1, ord_l2 with
  | [], _ -> true
  | _, [] -> false
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> false
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> includes_query_clause_order_list ord_l1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (_,qord1)::q1, (_,cord2)::q2 -> 
      if includes_query_order qord1 (SemIO,cord2)
      then includes_query_clause_order_list q1 q2
      else false

(** Similar to [includes_query_clause_relation] return [true] if [R(cord) \subseteq R(qord)]. *)
let includes_query_clause q_ord_fun cl_ord_fun = match q_ord_fun, cl_ord_fun with
  | QONone, _ -> true
  | _, CONone -> false
  | QOMax qord, COMax cord -> includes_query_order qord (SemIO,cord)
  | QOMax qord, COSpecific cord -> List.exists (fun (_,ord2) -> includes_query_order qord (SemIO,ord2)) cord
  | _, COMax _ -> false
  | QOSpecific q_ord_l, COSpecific c_ord_l -> includes_query_clause_order_list q_ord_l c_ord_l

(** Intersection and union *)

let rec intersection_clause_order_list ord_l1 ord_l2 = match ord_l1, ord_l2 with
  | [], ord_l | ord_l, [] -> ord_l
  | (i1,ord)::q1, (i2,_)::q2 when i2 > i1 -> (i1,ord)::(intersection_clause_order_list q1 ord_l2)
  | (i1,_)::q1, (i2,ord)::q2 when i2 < i1 -> (i2,ord)::(intersection_clause_order_list ord_l1 q2)
      (* At this point, both lists start with (i,_) for the same i *)
  | (i,ord1)::q1, (_,ord2)::q2 -> 
      (i,if ord1 = Less || ord2 = Less then Less else Leq)::(intersection_clause_order_list q1 q2)

(** [intersection_clause ord1 ord2] returns a clause ordering relation [ord] such that:
    R(ord) \subseteq R(ord1), R(ord) \subseteq R(ord2) and R(ord1) \cap R(ord2) \subseteq R(ord). *) 
let intersection_clause ord_fun1 ord_fun2 = match ord_fun1, ord_fun2 with
  | CONone, ord_fun
  | ord_fun, CONone -> ord_fun
  | COMax ord1, COMax ord2 ->
      if ord1 = Less || ord2 = Less then COMax Less else COMax Leq
  | COMax _, ord_fun
  | ord_fun, COMax _ -> ord_fun
  | COSpecific ord_l1, COSpecific ord_l2 ->  COSpecific (intersection_clause_order_list ord_l1 ord_l2)


let intersection_query_order (sem1,ord1) (sem2,ord2) = 
  if sem1 = sem2
  then 
    if ord1 = Less || ord2 = Less then (sem1, Less) else (sem1, Leq)
  else 
    match sem1,sem2 with
      | SemIO, _ -> SemIO, ord1
      |  _, SemIO -> SemIO, ord2
      | SemPhaseLess, _ -> SemPhaseLess, ord1
      | _, SemPhaseLess -> SemPhaseLess, ord2
      | _ -> Parsing_helper.internal_error __POS__ "It should only remain here SemStd cases that is already covered."

let rec intersection_query_order_list ord_l1 ord_l2 = match ord_l1, ord_l2 with
  | [], ord_l | ord_l, [] -> ord_l
  | (i1,ord)::q1, (i2,_)::q2 when i2 > i1 -> (i1,ord)::(intersection_query_order_list q1 ord_l2)
  | (i1,_)::q1, (i2,ord)::q2 when i2 < i1 -> (i2,ord)::(intersection_query_order_list ord_l1 q2)
      (* At this point, both lists start with (i,_) for the same i *)
  | (i,ord1)::q1, (_,ord2)::q2 -> 
      (i,intersection_query_order ord1 ord2)::(intersection_query_order_list q1 q2)

(** Similar to [intersection_clause] but on query ordering relations. *)
let intersection_query ord_fun1 ord_fun2 = match ord_fun1, ord_fun2 with
  | QOSpecific ord_l1, QOSpecific ord_l2 -> QOSpecific (intersection_query_order_list ord_l1 ord_l2)
  | ((QOSpecific ord_l) as ord_fun), _ | _, ((QOSpecific ord_l) as ord_fun) -> ord_fun
  | QOMax ord1, QOMax ord2 -> QOMax (intersection_query_order ord1 ord2)
  | ((QOMax ord) as ord_fun), _ | _, ((QOMax ord) as ord_fun) -> ord_fun
  | QONone, QONone -> QONone

let rec union_clause_order_list ord_l1 ord_l2 = match ord_l1, ord_l2 with
  | [], _ | _, [] -> []
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> union_clause_order_list q1 ord_l2
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> union_clause_order_list ord_l1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (i,ord1)::q1, (_,ord2)::q2 -> 
      (i,if ord1 = Leq || ord2 = Leq then Leq else Less)::(union_clause_order_list q1 q2)

(** [union_clause rel1 rel2] returns a clause ordering relation [rel] such that:
    R(rel1) \cup  R(rel2) \subseteq R(rel)). *)      
let union_clause ord_fun1 ord_fun2 = match ord_fun1, ord_fun2 with
  | CONone, _ | _, CONone -> CONone
  | COMax ord1, COMax ord2 -> if ord1 = Leq || ord2 = Leq then COMax Leq else COMax Leq
  | COMax Less, COSpecific ord_l | COSpecific ord_l, COMax Less 
    when List.for_all (function (_,Leq) -> true | _ -> false) ord_l -> COMax Leq
  | COMax ord, _ | _, COMax ord -> COMax ord (* Since the case above is excluded, 
             when ord = Less, the other order is COSpecific ord_l with at least one Less element
	     in ord_l, so COMax Less is correct *)
  | COSpecific ord_l1, COSpecific ord_l2 -> 
      let ord_l = union_clause_order_list ord_l1 ord_l2 in
      if ord_l = []
      then
        if 
          (List.exists (function (_,Less) -> true | _ -> false) ord_l1) && 
          (List.exists (function (_,Less) -> true | _ -> false) ord_l2)
        then COMax Less
        else COMax Leq 
      else COSpecific ord_l

let union_clause_list = function
  | t::q -> List.fold_left union_clause t q
  | [] -> Parsing_helper.internal_error __POS__ "Union cannot be applied on an empty list since our order does not have a representation for empty."

let union_clause_map2 f l1 l2 = match l1, l2 with
  | t1::q1, t2::q2 -> List.fold_left2 (fun acc t1' t2' -> union_clause acc (f t1' t2')) (f t1 t2) q1 q2
  | _ -> Parsing_helper.internal_error __POS__ "The lists should have the same size and non-empty."

let union_query_order (sem1,ord1) (sem2,ord2) = 
  let sem = match sem1,sem2 with
    | SemStd, _ | _, SemStd -> SemStd
    | SemPhaseLess, _ | _, SemPhaseLess -> SemPhaseLess
    | _ -> SemIO
  in
  let ord = if ord1 = Leq || ord2 = Leq then Leq else Less in
  (sem,ord)

let rec union_query_order_list ord_l1 ord_l2 = match ord_l1, ord_l2 with
  | [], _ | _, [] -> []
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> union_query_order_list q1 ord_l2
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> union_query_order_list ord_l1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (i,ord1)::q1, (_,ord2)::q2 -> 
      (i,union_query_order ord1 ord2)::(union_query_order_list q1 q2)

(** Similar to [union_clause]. *)
let union_query ord_fun1 ord_fun2 = match ord_fun1, ord_fun2 with
  | QONone, _ | _, QONone -> QONone
  | QOMax ord1, QOMax ord2 -> QOMax (union_query_order ord1 ord2)
  | QOMax ord, QOSpecific ord_l | QOSpecific ord_l, QOMax ord ->
      let ord_inter = List.fold_left (fun acc (_,ord) -> intersection_query_order acc ord) (SemStd,Leq) ord_l in
      QOMax (union_query_order ord ord_inter)
  | QOSpecific ord_l1, QOSpecific ord_l2 ->
      let ord_l = union_query_order_list ord_l1 ord_l2 in
      if ord_l = []
      then 
        let ord_inter1 = List.fold_left (fun acc (_,ord) -> intersection_query_order acc ord) (SemStd,Leq) ord_l1 in
        let ord_inter2 = List.fold_left (fun acc (_,ord) -> intersection_query_order acc ord) (SemStd,Leq) ord_l2 in
        QOMax (union_query_order ord_inter1 ord_inter2)
      else QOSpecific ord_l

let union_query_list = function
  | t::q -> List.fold_left union_query t q
  | [] -> Parsing_helper.internal_error __POS__ "Union cannot be applied on an emptylist since our order does not have a representation for empty."

let union_query_map2 f l1 l2 = match l1, l2 with
  | t1::q1, t2::q2 -> List.fold_left2 (fun acc t1' t2' -> union_query acc (f t1' t2')) (f t1 t2) q1 q2
  | _ -> Parsing_helper.internal_error __POS__ "The lists should have the same size and non-empty."

(** Predicates allowed to be ordered. *)

(* Block-predicate of user-defined predicate cannot be ordered:
   such predicates are added by lemmas and lemmas that conclude user-defined predicates
   just prove logical properties without any ordering constraints. *)
let can_predicate_have_clause_ordering_relation p =
  if p == Param.event_pred_block || p == Param.inj_event_pred_block || p == Param.event2_pred_block || p == Param.event_pred || p == Param.inj_event_pred || p == Param.event2_pred
  then true
  else
    match p.p_info with
      | Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _ | UserPred _ -> true
      | Block { p_info = Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _ ; _ } -> true
      | _ -> false
  
let can_fact_have_clause_ordering_relation = function
  | Pred(p,_) -> can_predicate_have_clause_ordering_relation p
  
let can_predicate_have_query_ordering_relation p = 
  if p == Param.event_pred_block || p == Param.inj_event_pred_block || p == Param.event2_pred_block || p == Param.event_pred || p == Param.inj_event_pred || p == Param.event2_pred
  then true
  else
    match p.p_info with
      | Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _ -> true
      | _ -> false

let can_fact_have_query_ordering_relation = function
  | Pred(p,_) -> can_predicate_have_query_ordering_relation p

(* We allow ordering constraints saying that
   a user-defined predicate happens before another user-defined predicate
   and a non user-defined predicate happens before another non user-defined predicate.
   We never say that a non user-defined predicate happens before a user-defined predicate because there are no clauses with a non user-defined predicate in hypothesis (except equal, which is not ordered) and a user-defined predicate in the conclusion.
   The following function forbids saying that a user-defined predicate happens before a non user-defined predicate. (The ordering for user-defined predicate relies on the length of the derivation, while the ordering for non user-defined predicates relies on the length of the trace.) *)
let can_hyp_and_concl_be_ordered hyp concl = match hyp,concl with
  | Pred(p_h,_), Pred(p_c,_) -> can_predicate_have_clause_ordering_relation p_h && (Terms.is_user_defined p_c || not (Terms.is_user_defined p_h))
	[@ppwarning "Vincent: if we say that user-defined predicates are always before other predicates, then the second conjunct above disappears and the function reduces to [can_predicate_have_clause_ordering_relation]"]
	
(** Some transformations *)

let enforce_strict_clause_ordering_relation = function
  | CONone -> CONone
  | COMax _ -> COMax Less
  | COSpecific c_ord_l -> COSpecific (List.map (fun (i,_) -> (i,Less)) c_ord_l)

let relax_to_leq_query_ordering_relation = function 
  | QONone -> QONone
  | QOMax _ -> QOMax (SemStd,Leq)
  | QOSpecific ord_l -> QOSpecific (List.map  (fun (i,_) -> (i,(SemStd,Leq))) ord_l)

let create_ordering_with_conclusion n = function
  | Pred(p,_) when can_predicate_have_clause_ordering_relation p -> COSpecific [n,Leq]
  | _ -> CONone

(** Compose clause relations *)

let compose_clause crel1 crel2 = match crel1 with
  | CONone -> CONone
  | COSpecific [1,Less] -> enforce_strict_clause_ordering_relation crel2
  | COSpecific [1,Leq] -> crel2
  | _ -> Parsing_helper.internal_error __POS__ "[compose_clause] Unexpected ordering."

(** Multiset ordering *)

(** [steps_strictly_before crel_list (n_std1,n_user1) (n_std2,n_user2)] returns [true] if for all pairs
    (MSet_Std1,MSet_User1) and (MSet_Std2,MSet_User) satisfying [crel_list], we have:
      (MSet_Std1,MSet_User1) < (MSet_Std2,MSet_User)
    - [n_std1] and [n_std2] indicates the number of standard facts we consider (|MSet_Std1| = n_std1 and |MSet_Std2| = n_std2)
    - [n_user1] and [n_user2] indicates the number of user-defined facts we consider (|MSet_User1| = n_user1 and |MSet_User2| = n_user2)

    The i-th element (from 1) of [crel_list] corresponds to the relation of the i-th element of facts with steps from (MSet_Std1,MSet_User1).
    The [n_std1] first elements of [crel_list] correspond to the facts from MSet_Std1.
    Similarly, in each relation from [crel_list], the indices less than [n_std2] refer to the facts with steps from MSet_Std2.
*)

let all_strict na nb =
  List.for_all (function 
    | COMax Less -> true
    | COSpecific ord_l -> List.exists (function (i,Less) when na <= i && i <= nb -> true | _ -> false) ord_l
    | _ -> false
  )

let distinct_pairwise_leq_ordering na nb crel_l =
  (* We check that each matched hypothesis are pairwise less or equal to one of a premise of the query. *)
  let rec all_distinct accu = function
    | [] -> true
    | COSpecific ord_l::q -> all_distinct_one accu q ord_l
    | _ -> false

  and all_distinct_one accu rest = function
    | [] -> false
    | (n,_)::q ->
        if n > nb 
        then false (* Since the list is ordered increasingly, we can stop there *)
        else
        if n < na || List.mem n accu
        then all_distinct_one accu rest q
        else
          if all_distinct (n::accu) rest
          then true
          else all_distinct_one accu rest q
  in

  all_distinct [] crel_l

let distinct_pairwise_leq_with_one_less_ordering na nb crel_l =
  (* We check that each matched hypothesis are pairwise less or equal to one of a premise of the query and at least one is strictly less.
    When we managed to find a matching that is equal but not strict, we record it in found_equal.
  *)
  let rec all_distinct one_less accu = function
    | [] -> one_less
    | COSpecific ord_fun::q -> all_distinct_one one_less accu q ord_fun
    | _ -> false

  and all_distinct_one one_less accu rest = function
    | [] -> false
    | (n,order)::q ->
        if n > nb 
        then false (* Since the list is ordered increasingly, we can stop there *)
        else
          if n < na || List.mem n accu
          then all_distinct_one one_less accu rest q
          else
            if all_distinct (one_less || order = Less) (n::accu) rest
            then true
            else all_distinct_one one_less accu rest q
  in
  all_distinct false [] crel_l

let strict_ordering nb_fact1 nb_fact2 na2 nb2 crel_l =
  nb_fact2 > 0 && (
    all_strict na2 nb2 crel_l ||
    (nb_fact1 = nb_fact2 && distinct_pairwise_leq_with_one_less_ordering na2 nb2 crel_l) ||
    (nb_fact1 < nb_fact2 && distinct_pairwise_leq_ordering na2 nb2 crel_l)
  )

let steps_strictly_before crel_l (nb_std1,nb_user1) (nb_std2,nb_user2) =  
  let (crel_std_l,crel_user_l) = List.split_nth nb_std1 crel_l in

  let (ia_std2,ib_std2,ia_user2,ib_user2) = 1, nb_std2, nb_std2+1, nb_std2 + nb_user2 in

  if strict_ordering nb_std1 nb_std2 ia_std2 ib_std2 crel_std_l
  then true
  else
    nb_std1 = nb_std2 &&
    distinct_pairwise_leq_ordering ia_std2 ib_std2 crel_std_l &&
    strict_ordering nb_user1 nb_user2 ia_user2 ib_user2 crel_user_l

  
(** Managing Ordering Data *)

let generate_empty_ordering_data () = 
  { ord_target = QONone; ord_proved = ref None; temp_var = None }

(** [are_ordering_proofs_recorded] indicates whether or not the ordering proofs need to be recorded.
    It is typically set to [true] when proving a lemma and [false] otherwise. *)
let are_ordering_proofs_recorded = ref false

(** A list of the references that has been modified as well as their previous value. 
    This is used during the verification of the query as we need to be able to backtrack
    on what was proved (typically when a "Unify" is raised). *)
let current_ordering_relation_proved = ref []

let rec reset_current_ordering_relation_proved tmp cur = 
  if tmp == cur
  then current_ordering_relation_proved := tmp
  else 
    match cur with
      | [] -> Parsing_helper.internal_error __POS__ "[reset_cbop] Unexpected empty list"
      | (r,old_ord)::q ->
          r.ord_proved := old_ord;
          reset_current_ordering_relation_proved tmp q 

let auto_cleanup_ordering_proof f = 
  let tmp = !current_ordering_relation_proved in

  try
    let r = f () in
    reset_current_ordering_relation_proved tmp !current_ordering_relation_proved;
    r
  with x -> 
    reset_current_ordering_relation_proved tmp !current_ordering_relation_proved;
    raise x

(** [update_proof ord_data qrel] update the proved ordering of [ord_data] with [qrel]. It records the previous
    proof in [current_ordering_relation_proved]. *)
let update_proof ord_data new_proved_qrel = 
  current_ordering_relation_proved := (ord_data,!(ord_data.ord_proved)) :: !current_ordering_relation_proved;
  ord_data.ord_proved := Some(new_proved_qrel)

(** A list of the ordering data in the query to be proved. Typically, before
    trying to verify a query, we save in [saved_ordering_data_to_prove] the ordering data
    that we are trying to prove. When a query is proved (typically in the scope of 
    [auto_cleanup_ordering_proof]), we update the list with the proved relation. When the program
    is out of the scope of the  [auto_cleanup_ordering_proof], the proof results in the ordering data
    have been reset but we use the content of [saved_ordering_data_to_prove] to definitely
    record the proof results. *)
let saved_ordering_data_to_prove = ref []

let initialise_recording_event = function
  | QSEvent(_,ord_data,_,_)
  | QSEvent2(ord_data,_,_)
  | QFact(_,ord_data,_) -> 
      assert(!(ord_data.ord_proved) = None);
      saved_ordering_data_to_prove := (ord_data,None) :: !saved_ordering_data_to_prove
  | _ -> ()

let rec initialise_recording_concl = function
  | QEvent ev -> initialise_recording_event ev
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> 
      initialise_recording_concl concl1;
      initialise_recording_concl concl2
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[initialise_recording_conl] Should only record lemma hence non nested."
  | _ -> ()

(** [initialise_record rq] needs to be called before proving the query [rq]. *)
let initialise_recording = function
  | Before(_,concl) -> 
      if !are_ordering_proofs_recorded
      then initialise_recording_concl concl

(** [record_proved_ordering ()] needs to be called once a query has been proved within the scope of the [auto_cleanup] *)
let record_proved_ordering () = 
  saved_ordering_data_to_prove := List.map (fun (ord_data,_) -> (ord_data,!(ord_data.ord_proved))) !saved_ordering_data_to_prove

(** [update_proved_ordering ()] needs to be called once a query has been proved outside of the [auto_cleanup] to 
    definitely record the proved ordering. *)
let update_proved_ordering () = 
  List.iter (fun (ord_data,ord_fun) -> ord_data.ord_proved := ord_fun) !saved_ordering_data_to_prove

(** [cleanup_proved_ordering_when_not_true ()] is called when an attack on the query and it remove the 
    recorded proofs as they are not valid. *) 
let cleanup_proved_ordering_when_not_true () = 
  List.iter (fun (ord_data,_) -> ord_data.ord_proved := None) !saved_ordering_data_to_prove

(** [cleanup_ordering ()] is called before returning the result of the query. When the query is true
    then the recorded proved ordering can be preserved. *) 
let cleanup_ordering () = 
  saved_ordering_data_to_prove := []
  

(* [cleanup_proved_ordering ()] removes the recorded proofs inside a query. When proving a group of lemmas by induction
    with [MaxSubset], a query can have a [True] result that is invalided when the inductive hypotheses are not all
    proved. In such a case, we have to prove again the query which requires to clean the recorded proofs before. *)

let cleanup_proved_ordering_data ord_data = ord_data.ord_proved := None

let cleanup_proved_ordering_event = function
  | QSEvent(_,ord_data,_,_) 
  | QSEvent2(ord_data,_,_) 
  | QFact(_,ord_data,_) -> cleanup_proved_ordering_data ord_data
  | ev -> ()

let rec cleanup_proved_ordering_concl = function
  | QEvent ev -> cleanup_proved_ordering_event ev
  | NestedQuery(_) -> ()
  | QAnd(concl1,concl2) 
  | QOr(concl1,concl2) -> 
      cleanup_proved_ordering_concl concl1;
      cleanup_proved_ordering_concl concl2
  | concl -> ()

let cleanup_proved_ordering_realquery = function
  | Before(evl,concl) -> cleanup_proved_ordering_concl concl

let cleanup_proved_ordering = function
  | RealQuery(rq,_) -> cleanup_proved_ordering_realquery rq
  | _ -> ()

(* Consider the ordering target proved. *)

let get_vars_option vars = function
  | None -> ()
  | Some t -> Terms.get_vars_acc vars t

let get_fixed_vars_in_premise evl = 
  let acc_vars = ref [] in
  List.iter (function
    | QSEvent(_,_,occ,ev) ->
        get_vars_option acc_vars occ;
        Terms.get_vars_acc acc_vars ev
    | QSEvent2(_,ev1,ev2) ->
        Terms.get_vars_acc acc_vars ev1;
        Terms.get_vars_acc acc_vars ev2
    | QFact({ p_info = Mess _ | MessBin _ | Table _ | TableBin _},_,args) ->
        List.iter (Terms.get_vars_acc acc_vars) args
    | _ -> ()
  ) evl;
  !acc_vars

let rec contains_only_fixed_vars fixed_vars = function
  | Var v -> List.memq v fixed_vars
  | FunApp(_,args) -> List.for_all (contains_only_fixed_vars fixed_vars) args

let order_map f prem_list ord_list = 
  let rec go_through i prem_list ord_list = match prem_list, ord_list with
    | _, [] -> []
    | _::q, (j,_)::_ when i != j -> go_through (i+1) q ord_list
    | e::q, (i,ord)::q_ord -> (f i e ord) :: go_through (i+1) q q_ord
    | _ -> Parsing_helper.internal_error __POS__ "[order_map] Unexpected list structure."
  in
  go_through 1 prem_list ord_list

[@ppwarning "Vincent: in assume_proved_*, you might want to just copy ord_target into
 ord_proved, and use one generic function to simplify lemmas. (Lemma.transl_realquery
 could be a good place for that function"]

(* We could improve the test by doing unification instead of just checking the event symbol.
   Need to check whether it's ok do it it at that time w.r.t. bound names. *)
let assume_proved_ordering_data_event evl_prem ev ord_data = 
  let ord_proved = match ord_data.ord_target with
    | QONone -> QONone
    | QOMax (SemStd,Less) -> QOMax (SemIO,Less)
    | QOMax (SemStd,Leq) ->
        let f_ev = Terms.get_root ev in
        if 
          List.for_all (function 
            | QSEvent(_,_,_,ev') | QSEvent2(_,ev',_) -> (Terms.get_root ev') != f_ev
            | QFact({ p_info = Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _ | Subterm _; _},_,_) -> true
            | QFact _ -> 
                (* In such a case, we have user defined predicates. It should not be possible. *)
                Parsing_helper.internal_error __POS__ "An event should not be before a user defined predicate."
            | _ -> 
                (* In all other cases, we have a constraint so they do not count in the order. *)
                true
          ) evl_prem
        then QOMax (SemIO,Less)
        else QOMax (SemIO,Leq)
    | QOMax _ -> Parsing_helper.internal_error __POS__ "In a query, we can only request with Standard semantics." 
    | QOSpecific ord_l ->
        let f_ev = Terms.get_root ev in
        let ord_l' = 
          order_map (fun i ev ord -> match ev with
            | QSEvent(_,_,_,FunApp(f,_)) | QSEvent2(_,FunApp(f,_),_) -> 
                if ord = (SemStd,Leq) && f == f_ev then i, (SemIO,Leq) else i, (SemIO,Less)
            | QFact({ p_info = Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _; _},_,_) -> i, (SemIO,Less)
            | _ -> 
                (* In such a case, we have user defined predicates or subterm or constraints. It should not be possible. *)
                Parsing_helper.internal_error __POS__ "An event should not be before a user defined predicate / subterm / constraints."
          ) evl_prem ord_l
        in
        QOSpecific ord_l'
  in
  ord_data.ord_proved := Some ord_proved
  
(* When a fact table(M)@i phase n occurs in the conclusion of a query and F@j in the premise of the query.
  The semantics satisfied by table(M)@i refers to |-_{Std}. Thus, if n = 0 then we have an equivalence with |-_{IO}.
  If n > 0 then we have to consider |-_{Std}. In such a case, if F is:
    - an event then we can only use |-_{Std} as the event can be from a phase smaller than n. Note that we could
    have used |-_{IO} if we could have used an "existential" value for the phase.
    - an 'mess(M,N) phase m' then we can use |-_{IO} if m >= n.
    - an 'attacker(M,N) phase m' then we can use |-_{IO} if m >= n.
    - an 'table(M') phase m' then we can use |-_{IO} if m >= n. Moreover, if M and M' are not unifiable then we can guarantee strict
      order. 
*)
let assume_proved_ordering_data_table evl_prem tbl_phase tbl ord_data =

  (* [create_order fact_prem] returns [b_IO,b_strict] where [b_IO] is true when the satisfaction relation |-_{IO} can be used.
     Moreover, [b_strict] is true when [b_IO = true] and the relation is sure to be strict.  *)
  let create_order is_strict = function
    | QFact({ p_info = Table n | TableBin n;_},_,tbl'::_) -> 
        if tbl_phase = 0 || n >= tbl_phase 
        then
          if is_strict || (Terms.get_root tbl') != (Terms.get_root tbl) 
          then (SemIO,Less)
            (* We do something weaker then unification as it's not completely clear what do do
            with bi-table and table. This current test could be improved in the future. *)
          else (SemIO,Leq)
        else (SemStd,Leq)
    | QFact({ p_info = Mess(n,_) | MessBin(n,_) | Attacker(n,_) | AttackerBin(n,_);_ },_,tbl'::_) -> 
        if tbl_phase = 0 || n >= tbl_phase
        then (SemIO,Less)
        else (SemStd,Leq)
    | QFact({ p_info = Subterm _; _},_,_) -> (SemIO,Less) (* Here it just indicate the strongest version *)
    | QFact _ -> 
        (* User defined predicates. Should have been discared before *)
        Parsing_helper.internal_error __POS__ "Should not have QOMax with user defined predicate in the premise."
    | _ -> 
        (* The rest are constraints so allowed*)
        (SemIO,Less)
  in

  let ord_proved = match ord_data.ord_target with
    | QONone -> QONone
    | QOMax (SemStd,ord) -> QOMax (List.fold_left (fun acc_ord fact -> union_query_order acc_ord (create_order (ord = Less) fact)) (SemIO,Less) evl_prem)
    | QOMax _ -> Parsing_helper.internal_error __POS__ "In a query, we can only request with Standard semantics." 
    | QOSpecific ord_l -> 
        let ord_l' = 
          order_map (fun i ev (sem,ord) -> 
            if SemStd <> sem 
            then Parsing_helper.internal_error __POS__ "Table should only be ordered with standard semantics.";
            (i,create_order (ord = Less) ev)
          ) evl_prem ord_l
        in
        QOSpecific ord_l'
  in
  ord_data.ord_proved := Some ord_proved

let assume_proved_ordering_data_attacker fixed_vars evl_prem att_phase att_term ord_data =
  if att_phase > 0 || not (List.for_all (contains_only_fixed_vars fixed_vars) att_term)
  then ord_data.ord_proved := Some (relax_to_leq_query_ordering_relation ord_data.ord_target)
  else
    let ord_proved = match ord_data.ord_target with
      | QONone -> QONone
      | QOMax (SemStd,ord) ->
          if 
            List.for_all (function 
              | QFact({ p_info = Attacker _ | AttackerBin _;_ },_,_) -> false
              | QFact({ p_info = Mess(n,_) | MessBin(n,_);_ },_,_) when n < att_phase || (ord = Leq && n = att_phase) -> false
              | _ -> true
            ) evl_prem
          then QOMax (SemIO,Less)
          else QOMax (SemPhaseLess,ord)
      | QOMax _ -> Parsing_helper.internal_error __POS__ "In a query, we can only request with Standard semantics." 
      | QOSpecific ord_l ->
          let ord_l' = 
            order_map (fun i ev (_,ord) -> match ev with
              | QFact({ p_info = Attacker _ | AttackerBin _;_ },_,_) -> i, (SemPhaseLess,ord)
              | QFact({ p_info = Mess(n,_) | MessBin(n,_);_ },_,_) when n < att_phase || (ord = Leq && n = att_phase) -> i, (SemPhaseLess,ord)
              | QSEvent _ | QSEvent2 _ -> i, (SemIO,Less)
              | QFact({ p_info = Mess _ | MessBin _ | Table _ | TableBin _; _},_,_) -> i, (SemIO,Less)
              | _ -> i, (SemStd,ord)
            ) evl_prem ord_l
          in
          QOSpecific ord_l'
    in
    ord_data.ord_proved := Some ord_proved
  
let assume_proved_ordering_data_mess evl_prem mess_phase ord_data =
  let ord_proved = match ord_data.ord_target with
    | QONone -> QONone
    | QOMax (SemStd,Less) -> QOMax (SemIO,Less)
    | QOMax (SemStd,ord) ->
        if 
          List.for_all (function 
            | QFact({ p_info = Mess (n,_) | MessBin (n,_);_ },_,_) -> n > mess_phase
            | QFact({ p_info = Attacker _| AttackerBin _;_ },_,_) -> false
            | _ -> true
          ) evl_prem
        then QOMax (SemIO,Less)
        else QOMax (SemIO,ord) 
    | QOMax _ -> Parsing_helper.internal_error __POS__ "In a query, we can only request with Standard semantics." 
    | QOSpecific ord_l ->
        let ord_l' = 
          order_map (fun i ev (_,ord) -> match ev with
            | QFact({ p_info = Mess (n,_) | MessBin (n,_);_ },_,_) when  n <= mess_phase -> i, (SemIO,ord) 
            | QFact({ p_info = Table _ | TableBin _ | Mess _ | MessBin _; _},_,_)
            | QSEvent _ | QSEvent2 _-> i, (SemIO,Less) 
            | _ -> i, (SemIO,ord) 
          ) evl_prem ord_l
        in
        QOSpecific ord_l'
  in
  ord_data.ord_proved := Some ord_proved
  
let assume_proved_event fixed_vars evl_prem = function
  | QSEvent(_,ord_data,_,ev)
  | QSEvent2(ord_data,ev,_) -> assume_proved_ordering_data_event evl_prem ev ord_data
  | QFact(p,ord_data,((t::_) as args)) -> 
      if can_predicate_have_query_ordering_relation p
      then 
        match p.p_info with
          | Attacker (i,_) | AttackerBin (i,_) -> assume_proved_ordering_data_attacker fixed_vars evl_prem i args ord_data
          | Table i | TableBin i -> assume_proved_ordering_data_table evl_prem i t ord_data
          | Mess (i,_) | MessBin (i,_) -> assume_proved_ordering_data_mess evl_prem i ord_data
          | _ -> 
              assert(ord_data.ord_target = QONone);
              ord_data.ord_proved := Some QONone
      else ord_data.ord_proved := Some QONone
  | _ -> ()

let rec assume_proved_concl_query fixed_vars evl_prem = function
  | QEvent ev -> assume_proved_event fixed_vars evl_prem ev
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[consider_proved_concl_query] Should not contained nested queries."
  | QAnd(concl1,concl2) 
  | QOr(concl1,concl2) -> 
      assume_proved_concl_query fixed_vars evl_prem concl1;
      assume_proved_concl_query fixed_vars evl_prem concl2
  | _ -> ()

let assume_proved_realquery = function
  | Before(evl,concl) -> 
      let fixed_vars = get_fixed_vars_in_premise evl in
      assume_proved_concl_query fixed_vars evl concl

let assume_proved = function
  | RealQuery(rq,_) -> assume_proved_realquery rq
  | _ -> ()
  
(* Refreshing of the ordering proofs references in the ordering data of the query,lemmas,restrictions and axioms. *)

let refresh_ordering_data_ref ord_data = 
  assert(!(ord_data.ord_proved) = None);
  assert(ord_data.temp_var = None);
  { ord_data with ord_proved = ref None }

let refresh_ordering_data_event = function
  | QSEvent(inj,ord_data,occ,ev) -> QSEvent(inj,refresh_ordering_data_ref ord_data,occ,ev)
  | QSEvent2(ord_data,ev1,ev2) -> QSEvent2(refresh_ordering_data_ref ord_data,ev1,ev2)
  | QFact(p,ord_data,args) -> QFact(p,refresh_ordering_data_ref ord_data,args)
  | ev -> ev

let rec refresh_ordering_data_concl = function
  | QEvent ev -> QEvent (refresh_ordering_data_event ev)
  | NestedQuery rq -> NestedQuery (refresh_ordering_data_realquery rq)
  | QAnd(concl1,concl2) -> QAnd(refresh_ordering_data_concl concl1,refresh_ordering_data_concl concl2)
  | QOr(concl1,concl2) -> QOr(refresh_ordering_data_concl concl1,refresh_ordering_data_concl concl2)
  | concl -> concl

and refresh_ordering_data_realquery = function
  | Before(evl,concl) -> 
      Before(List.map refresh_ordering_data_event evl,refresh_ordering_data_concl concl)

let refresh_ordering_data_in_realquery_e (rq,ext) =
  (refresh_ordering_data_realquery rq, ext)

let refresh_ordering_data_query_e = function
  | RealQuery(rq,pub_vars),ext -> RealQuery(refresh_ordering_data_realquery rq,pub_vars), ext
  | q_e -> q_e

let refresh_ordering_data_in_lemma = function
  | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[refresh_ordering_data_in_lemma] Should be translated by now."
  | Lemma lem_state ->
      let lemmas' = 
        List.map (fun lem ->
          { lem with ql_query = refresh_ordering_data_query_e lem.ql_query }
        ) lem_state.lemmas
      in
      Lemma { lem_state with lemmas = lemmas' }

let refresh_ordering_data_t_query = function
  | CorrespQuery(q_list,solve_status) -> CorrespQuery(List.map refresh_ordering_data_query_e q_list,solve_status)
  | CorrespQEnc (qorig_enc_list,solve_status) ->
      CorrespQEnc (List.map (fun (qorig,qenc) -> qorig, refresh_ordering_data_query_e qenc) qorig_enc_list, solve_status)
  | q -> q

let refresh_process_query = function
  | SingleProcess (desc,qlist) -> SingleProcess(desc,List.map refresh_ordering_data_t_query qlist)
  | SingleProcessSingleQuery (desc,q) -> SingleProcessSingleQuery(desc,refresh_ordering_data_t_query q)
  | pq -> pq

let refresh_ordering_data pi_state =
  { pi_state with
    pi_process_query = refresh_process_query pi_state.pi_process_query;
    pi_lemma = List.map refresh_ordering_data_in_lemma pi_state.pi_lemma;
    pi_original_axioms = List.map (fun (rq,b) -> refresh_ordering_data_in_realquery_e rq, b) pi_state.pi_original_axioms
  }

(** [setup_ordering_data_QMaxq_concl] is applied when the option is given that all facts in 
    the conclusion of a query occur before the premise. *)

let setup_ordering_data_QOMax ord ord_data = 
  assert(ord_data.ord_target = QONone );
  { ord_data with ord_target = ord }

let setup_ordering_data_QOMax_event ord = function
  | QSEvent(inj,ord_data,occ,ev) -> QSEvent(inj,setup_ordering_data_QOMax ord ord_data,occ,ev)
  | QSEvent2(ord_data,ev1,ev2) -> QSEvent2(setup_ordering_data_QOMax ord ord_data,ev1,ev2)
  | QFact(p,ord_data,args) as ev -> 
      if can_predicate_have_query_ordering_relation p
      then QFact(p,setup_ordering_data_QOMax ord ord_data,args)
      else ev
  | ev -> ev

let rec setup_ordering_data_QOMax_concl ord = function
  | QEvent ev -> QEvent (setup_ordering_data_QOMax_event ord ev)
  | NestedQuery(Before(evl,concl)) -> 
      NestedQuery(Before(List.map (setup_ordering_data_QOMax_event ord) evl,setup_ordering_data_QOMax_concl ord concl))
  | QAnd(concl1,concl2) -> QAnd(setup_ordering_data_QOMax_concl ord concl1,setup_ordering_data_QOMax_concl ord concl2)
  | QOr(concl1,concl2) -> QOr(setup_ordering_data_QOMax_concl ord concl1,setup_ordering_data_QOMax_concl ord concl2)
  | concl -> concl

let setup_ordering_data_QMaxq_ord time_vars ord_data f_apply = match ord_data.temp_var with
  | None ->
      let i = Terms.new_var "t" Param.time_type in 
      let ord_data' = { ord_data with temp_var = Some (Var i,Parsing_helper.dummy_ext) } in
      f_apply ord_data', fun concl -> QAnd(concl, QEvent(QMaxq (Var i,time_vars)))
  | Some (i,_) ->
      f_apply ord_data, fun concl -> QAnd(concl, QEvent(QMaxq (i,time_vars)))

let setup_ordering_data_QMaxq_event is_modified time_vars = function
  | QSEvent(inj,ord_data,occ,ev) -> 
      is_modified := true;
      setup_ordering_data_QMaxq_ord time_vars ord_data (fun ord_data -> QSEvent(inj,ord_data,occ,ev))
  | QSEvent2(ord_data,ev1,ev2) -> 
      is_modified := true;
      setup_ordering_data_QMaxq_ord time_vars ord_data (fun ord_data -> QSEvent2(ord_data,ev1,ev2))
  | QFact(p,ord_data,args) as ev -> 
      if can_predicate_have_query_ordering_relation p
      then 
        begin 
          is_modified := true;
          setup_ordering_data_QMaxq_ord time_vars ord_data (fun ord_data -> QFact(p,ord_data,args))
        end
      else ev, fun concl -> concl
  | ev -> ev, fun concl -> concl

let rec setup_ordering_data_QMaxq_concl is_modified time_vars = function
  | QEvent ev -> 
      let (ev',add_QMaxq) = setup_ordering_data_QMaxq_event is_modified time_vars ev in
      add_QMaxq (QEvent ev')
  | NestedQuery(Before([ev],concl)) -> 
      let concl' = setup_ordering_data_QMaxq_concl is_modified time_vars concl in
      let (ev',add_QMaxq) = setup_ordering_data_QMaxq_event is_modified time_vars ev in
      add_QMaxq (NestedQuery(Before([ev'],concl')))
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "[setup_ordering_data_QMaxq_concl] Premise of a nested query should only contain a single event."
  | QAnd(concl1,concl2) -> QAnd(setup_ordering_data_QMaxq_concl is_modified time_vars concl1,setup_ordering_data_QMaxq_concl is_modified time_vars concl2)
  | QOr(concl1,concl2) -> QOr(setup_ordering_data_QMaxq_concl is_modified time_vars concl1,setup_ordering_data_QMaxq_concl is_modified time_vars concl2)
  | concl -> concl

let rec compute_new_premise_time_vars_event ord_data f_apply q_ev = match ord_data.temp_var with
  | None -> 
      let i = Terms.new_var "t" Param.time_type in 
      let ord_data' = { ord_data with temp_var = Some (Var i,Parsing_helper.dummy_ext) } in
      let (i_list,q_ev') = compute_new_premise_time_vars q_ev in
      (Var i :: i_list, (f_apply ord_data')::q_ev')
  | Some (i,_) ->
      let (i_list,q_ev') = compute_new_premise_time_vars q_ev in
      (i :: i_list, (f_apply ord_data)::q_ev')

and compute_new_premise_time_vars = function
  | QSEvent(inj,ord_data,occ,ev)::q_ev ->
      compute_new_premise_time_vars_event ord_data (fun ord_data -> QSEvent(inj,ord_data,occ,ev)) q_ev
  | QSEvent2(ord_data,ev1,ev2)::q_ev ->
      compute_new_premise_time_vars_event ord_data (fun ord_data -> QSEvent2(ord_data,ev1,ev2)) q_ev
  | QFact(p,ord_data,args)::q_ev ->
      if can_predicate_have_query_ordering_relation p
      then compute_new_premise_time_vars_event ord_data (fun ord_data -> QFact(p,ord_data,args)) q_ev
      else ([],QFact(p,ord_data,args)::q_ev)
  | _ -> Parsing_helper.internal_error __POS__ "[setup_ordering_data_when_conclBeforePremise_premise] We should have it a fact with a predicate that cannot be ordered before."

let setup_ordering_data_when_conclBeforePremise_realquery = function
  | Before(evl,concl) -> 

      let only_can_be_ordered = 
        List.for_all (function
          | QFact(p,_,_) -> can_predicate_have_query_ordering_relation p
          | _ -> true
        ) evl
      in

      if only_can_be_ordered
      then
        let ord = match evl with
          | [] -> Parsing_helper.internal_error __POS__ "[setup_ordering_data_when_conclBeforePremise_realquery] Premise should not be empty."
          | _::(QSEvent _ | QSEvent2 _ | QFact _)::_ ->
              (* The premise contains at least 2 fact that can be ordered. *)
              QOMax (SemStd,Leq)
          | _ ->  QOSpecific [(1,(SemStd,Leq))]
        in
        Before(evl,setup_ordering_data_QOMax_concl ord concl)
      else
        let (time_vars,evl') = compute_new_premise_time_vars evl in
        let is_modified = ref false in
        let concl' = setup_ordering_data_QMaxq_concl is_modified time_vars concl in
        Before((if !is_modified then evl' else evl),concl')

let setup_ordering_data_when_conclBeforePremise_query = function
  | RealQuery(rq,pub_vars) -> RealQuery(setup_ordering_data_when_conclBeforePremise_realquery rq, pub_vars)
  | query -> query

let setup_ordering_data_when_conclBeforePremise_t_query = function
  | QueryToTranslate _ -> Parsing_helper.internal_error __POS__ "[setup_ordering_data_when_conclBeforePremise_t_query] Query should have been translated."
  | CorrespQuery(ql,solve) ->
      if solve.concl_before_premise
      then 
        let ql' = List.map (fun (q,e) -> setup_ordering_data_when_conclBeforePremise_query q, e) ql in
        CorrespQuery(ql',solve)
      else CorrespQuery(ql,solve)
  | CorrespQEnc _ 
  | ChoiceQEnc _ -> Parsing_helper.internal_error __POS__ "[setup_ordering_data_when_conclBeforePremise_t_query] Query should not have been encoded yet."
  | q -> q

let setup_ordering_data_when_conclBeforePremise pi_state =

  let process_query = match pi_state.pi_process_query with
    | Equivalence _ -> pi_state.pi_process_query
    | SingleProcess (desc,ql) -> SingleProcess(desc,List.map setup_ordering_data_when_conclBeforePremise_t_query ql)
    | SingleProcessSingleQuery(desc,q) -> SingleProcessSingleQuery(desc,setup_ordering_data_when_conclBeforePremise_t_query q)
  in
  
  assert(pi_state.pi_original_axioms = []);

  let pi_lemma = 
    List.map (function
      | LemmaToTranslate _ -> Parsing_helper.internal_error __POS__ "[setup_ordering_data_when_conclBeforePremise] Should have been already translated."
      | Lemma lem_state ->
          if lem_state.solve_status.concl_before_premise || not pi_state.pi_requires_liveness
          then
            let lemmas = 
              List.map (fun lem ->
                assert (lem.ql_original_query = None);
                { lem with ql_query = (setup_ordering_data_when_conclBeforePremise_query (fst lem.ql_query),snd lem.ql_query) }
              ) lem_state.lemmas
            in
            Lemma {lem_state with lemmas = lemmas }
          else Lemma lem_state
    ) pi_state.pi_lemma
  in

  { pi_state with pi_process_query = process_query; pi_lemma = pi_lemma }

(** Check that all ordering data are proved *)

let rec check_lemmas_are_proved_concl = function
  | QEvent(QSEvent(_,ord_data,_,_))
  | QEvent(QSEvent2(ord_data,_,_))
  | QEvent(QFact(_,ord_data,_)) -> 
      begin match !(ord_data.ord_proved)  with
        | None -> ()
        | Some ord ->
            if not (includes_query ord_data.ord_target ord)
            then Parsing_helper.internal_error __POS__ "[check_lemmas_are_proved_concl] The proved relation should by included in the target relation."
      end
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> 
      check_lemmas_are_proved_concl concl1; 
      check_lemmas_are_proved_concl concl2
  | _ -> ()

let check_lemmas_are_proved_query = function
  | RealQuery(Before(_,concl),_) -> check_lemmas_are_proved_concl concl
  | _ -> ()

let check_lemmas_are_proved = function
  | Lemma lem_state ->
      List.iter (fun lem -> 
        let (q,_) = lem.ql_query in
        check_lemmas_are_proved_query q
      ) lem_state.lemmas
  | _ -> ()

(* Check whether we require liveness or additional saturation *)

let record_events_preds_in_event is_concl_before_premise requires_liveness time_variables events preds = function
  | QSEvent(_,ord_data,_,FunApp(ev,_)) ->
      if not is_concl_before_premise
      then
        begin match ord_data.temp_var with
          | None -> requires_liveness := true;
          | Some (t,_) -> 
              if not (List.exists (Terms.equal_terms t) time_variables)
              then requires_liveness := true
        end;
      if List.for_all (fun (ev',_) -> ev != ev') !events
      then events := (ev,true) :: !events
  | QFact(p,ord_data,_) ->
      if can_predicate_have_query_ordering_relation p
      then 
        begin
          if not is_concl_before_premise
          then 
            begin match ord_data.temp_var with
              | None -> requires_liveness := true
              | Some (t,_) ->
                  if not (List.exists (Terms.equal_terms t) time_variables)
                  then requires_liveness := true
            end;
          if List.for_all (fun (p',_) -> p != p') !preds
          then preds := (p,true) :: !preds
        end
  | _ -> ()

let rec gather_conclusion f_next time_variables_prem = function
  | QEvent(QEq((t1,_),(t2,_))) when List.exists (Terms.equal_terms t1) time_variables_prem -> f_next [t2] []
  | QEvent(QEq((t1,_),(t2,_))) when List.exists (Terms.equal_terms t2) time_variables_prem -> f_next [t1] []
  | QEvent(QGeq((t1,_),(t2,_)))
  | QEvent(QGr((t1,_),(t2,_))) when List.exists (Terms.equal_terms t1) time_variables_prem -> f_next [t2] []
  | QEvent(ev) -> f_next [] [ev]
  | QAnd(concl1,concl2) ->
      gather_conclusion (fun vars1 evl1 ->
        gather_conclusion (fun vars2 evl2 ->
          f_next (vars1@vars2) (evl1@evl2)
        ) time_variables_prem concl2
      ) time_variables_prem concl1
  | QOr(concl1,concl2) ->
      gather_conclusion f_next time_variables_prem concl1;
      gather_conclusion f_next time_variables_prem concl2
  | QTrue | QFalse | QConstraints _ -> f_next [] [] (* no ordering in constraints *)
  | NestedQuery _ -> Parsing_helper.internal_error __POS__ "Restrictions should not contain nested queries."

let retrieve_time_variables = function
  | QSEvent(_,ord_data,_,_) | QFact(_,ord_data,_) -> 
      begin match ord_data.temp_var with
        | Some (t,_) -> Some t
        | None -> None
      end
  | _ -> None

(* This function is applied before encoding. Hence we cannot rely on the target query 
   ordering. We currently rely on the option [conclBeforePremise] but this could be 
   better detected in the future by looking at the time variables *)
let requires_liveness_and_additional_saturation pi_state = 
  let events = ref pi_state.pi_events_to_solve_twice in
  let preds = ref pi_state.pi_predicates_to_solve_twice in
  let requires_liveness = ref false in

  List.iter (function
    | Lemma { is_axiom = KRestriction; lemmas = lem_l; solve_status; _ } ->
        List.iter (fun lem -> match lem.ql_query with
          | RealQuery(Before(evl,concl),_),_ -> 
              let time_variables = List.filter_map retrieve_time_variables evl in
              gather_conclusion (fun vars factl ->
                List.iter (record_events_preds_in_event solve_status.concl_before_premise requires_liveness vars events preds) factl
              ) time_variables concl
          | _ -> ()
        ) lem_l
    | _ -> ()
  ) pi_state.pi_lemma;


  let pi_state' = 
    { pi_state with
      pi_events_to_solve_twice = !events;
      pi_predicates_to_solve_twice = !preds;
      pi_requires_liveness = !requires_liveness
    }
  in

  setup_ordering_data_when_conclBeforePremise pi_state'

(* Verification *)

let query_of_clause = function
  | CONone -> QONone
  | COMax Less -> QOMax (SemIO,Less)
  | COMax Leq -> QOMax (SemIO,Leq)
  | COSpecific ord_l -> 
      QOSpecific (
        List.map (function
          | (i,Less) -> (i,(SemIO,Less))
          | (i,Leq) -> (i,(SemIO,Leq))
        ) ord_l
      )

(** In [verify_and_update_ordering_data_IO f_next ord_data crel] the query fact with ordering data
    [ord_data] has been instantiated with a matching fact of the hypotheses of the clause with ordering
    relation [crel]. The ordering data [ord_data] is updated if [crel] is included in the target ordering. 
    @raise Unify if the [crel] is not included in the target ordering of [ord_data]. *)    
let verify_and_update_ordering_data_IO f_next ord_data crel = 
  (* Checking that the query ordering function is implied by the target ordering function (i.e. )*)
  if not (includes_query_clause ord_data.ord_target crel)
  then raise Unify;
  
  if !are_ordering_proofs_recorded
  then 
    match !(ord_data.ord_proved) with
      | None ->
          auto_cleanup_ordering_proof (fun () ->
            update_proof ord_data (query_of_clause crel);
            f_next ()
          )
      | Some qrel -> 
          let qrel' = union_query qrel (query_of_clause crel) in
          if qrel = qrel'
          then 
            (* Nothing changed *)
            f_next ()
          else 
            auto_cleanup_ordering_proof (fun () ->
              update_proof ord_data qrel';
              f_next ()
            )
  else f_next ()

let update_ordering_data_list f_next fact_ord_data_l new_qrel = 
  let was_modified = ref false in
  let new_qrel_proved = 
    List.map (fun (_,ord_data) -> match !(ord_data.ord_proved) with
      | None -> 
          was_modified := true;
          Some new_qrel
      | Some qrel -> 
          let qrel' = union_query qrel new_qrel in
          if qrel <> qrel'
          then
            begin 
              was_modified := true;
              Some qrel'
            end
          else None
    ) fact_ord_data_l
  in
  if !was_modified
  then
    auto_cleanup_ordering_proof (fun () ->
      List.iter2 (fun (_,ord_data) -> function
        | None -> ()
        | Some qrel -> update_proof ord_data qrel
      ) fact_ord_data_l new_qrel_proved;
      
      f_next ()
    )
  else f_next ()

(** [update_ordering_data_list_semantics f_next fact_ord_data_l sem] is called after the query facts in 
    [fact_ord_data_l] are proved with the semantics [sem]. The function updates the proofs of the 
    ordering data with the relation corresponding to [sem] semantics.
    @warning All the target ordering in [fact_ord_data_l] must be the same. 
    @warning [sem] must be either [SemPhaseless] or [SemStd] *)  
let update_ordering_data_list_semantics f_next fact_ord_data_l crel_opt sem =
  if !are_ordering_proofs_recorded
    then 
      let qrel_phase = match crel_opt with 
        | Some crel -> 
            Parsing_helper.debug (fun () ->
              Parsing_helper.debug_msg "Update ordering data: ";
              print_string "[DEBUG] ";
              Debug.display_clause_ordering_relation crel;
              print_string "\n"
            );
            begin match crel with
            | CONone -> QONone
            | COMax ord -> QOMax (sem,ord)
            | COSpecific ord_l -> QOSpecific(List.map (fun (i,ord) -> (i,(sem,ord))) ord_l)
            end
        | None -> 
            Parsing_helper.debug (fun () ->
              Parsing_helper.debug_msg "Update ordering data: None";
            );
            match fact_ord_data_l with
            | [] -> Parsing_helper.internal_error __POS__ "Should contain at least one element."
            | (_,ord_data)::_ ->
                match ord_data.ord_target with
                | QONone -> QONone
                | QOMax (_,ord) -> QOMax (sem,ord)
                | QOSpecific ord_l -> QOSpecific (List.map (fun (i,(_,ord)) -> (i,(sem,ord))) ord_l)
      in
      update_ordering_data_list f_next fact_ord_data_l qrel_phase
    else f_next ()
