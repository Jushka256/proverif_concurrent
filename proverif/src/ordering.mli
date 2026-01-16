open Types
open Pitypes

(* Predicates to prove *)

val initialise_pred_to_prove : predicate list -> unit

val reset_pred_to_prove : unit -> unit

val is_pred_to_prove : predicate -> bool

val is_pred_to_prove_fact : fact -> bool

(** Ordering in a clause always correspond to the IO-satisfaction relation:
  In  [F@i && H -> C@j], we know that if the clause is used then
    - T |-_{IO} F@i
    - T |-_{IO} C@j
  Moreover, if the order is Less (resp. Leq) then i < j (resp. i <= j).

  When the conclusion is a conjunction of facts then an hypothesis can be ordered
  with respect to each fact in the conclusion using COSpecific.

  @warning We consider the following invariant: When the conclusion is a single
  fact then COSpecific [1,ord] is used rather than COMax ord even though they would 
  have been semantically equal.
*)

(** Ordering in a query may correspond to several semantics. In a correspondence query, 
  [F_1@i_1 && .. && F_n@i_n ==> \psi[G@k]], the semantics of the premise corresponds to the 
  IO-satisfaction relation but the satisfaction relation of G@k may vary. In particular,
  it can use
    - Standard relation |-_{i}
    - Phaseless relation |-_{p} where attacker and table facts cannot rely on rules I-Phase
      to prove their satisfaction (it can still rely on I-App and I-New)
    - IO relation |-_{IO}
  Note that |-_{IO} \subseteq |-_{p} \subseteq |-_{i}. 
  {[
    type satisfaction_semantics =
      | SemIO
      | SemPhaseLess
      | SemStd

    type query_order = satisfaction_semantics * clause_order
  ]}
*)

(** Both clause and query ordering relations are in fact binary relations R on fact * (fact*int) list 
    where {% (F,[C1@k_1,...,Cn@k_n]) \in R %} if they satisfy the given constraints. For example:
    if [ord_rel = QOMax (SemPhaseLess * Less)] then (F,[C1@k_1,...,Cn@k_n]) \in R iff
    there exists i such that 
    - i < max(k_1,...,k_n)
    - T |-_{IO} Cj@k_j for all j
    - T |-_{p} F@i
    Note that the satisfaction relation of the conclusion facts is always |-_{IO}. The satisfaction relation of
    F is given by the [query_order]. Consider [ord_rel = QOSpecific [ (1,(SemStd,Leq)); (3,(SemIO,Less)) ]]. Then 
    (F,[C1@k_1,...,Cn@k_n]) \in R iff there exist i_1,i_3 such that 
    - n >= 3
    - T |-_{IO} Cj@k_j for all j
    - T |-_{i} F@i_1 and i_1 <= k_1
    - T |-_{IO} F@i_3 and i_3 < k_3
    We will denote [R(ord_rel)] the induced relation by [ord_rel].

    Due to the semantics in [query_order], we consider the following syntactic invariants on the queries :
      - Equalities and disequalities (<>) of time variables can only occur between two events
      - User defined predicates do not have time variables
      - Strict time inequalities (<) cannot occur between two attacker facts. ProVerif will never be able 
        to prove it directly. It can be indirectly inferred by showing that an intermediary non-attacker fact
        occurs between the two attacker facts.
      - Inequalities (<=) cannot involve user-defined predicates.

    Relations between the different orderings:
      - |-_{IO} \subseteq |-_{p} \subseteq |-_i
      - If F is not an attacker fact, then T |-_{IO} F@i_1 iff T |-_p F@i_1
      - If F is an attacker fact, then there is no total order with the [query_order]. For instance,
          \exists i_1. T |-_{IO} F@i_1 and i_1 <= k   
        and   
          \exists i_1. T |-_p F@i_1 and i_1 < k
        are not comparable (in term of implication). 
    
    We restrict the set of (bi)traces we consider to the set of IO-compliant trace T such that:
      For all lemmas F_1@i_1 && .. && F_n@i_n && \phi ==> \psi[G@k], for all \sigma, for all
      attacker fact G in \psi
        if 
          1) G is an attacker fact such that \vars(G) \subseteq \vars(F_j | j=1..n && F_j is a 
            table fact, event, mess fact). We say that G is variable-safe
          2) T \satisfy (F_j@i_j)\sigma for j = 1..n; and
          3) T \satisfy_i (G@k)\sigma
        then there k' such that T \satisfy_{IO} (G\sigma)@k' and if k' > k\sigma then 
          the steps between k\sigma and k' in T are all applications of functions
    
    The first property ensures that we can always transform any IO-compliant trace T into one that 
    satisfies this invariant. Without this first property, there are cases where only infinite traces
    could satisfy the conclusion.

    This invariant allows us to deduce the following properties: Consider T |-_p F@i and T |-_{IO} C@j
    where F is variable-safe.
      1) We first deduce that F is necessarily an attacker fact (otherwise we would have T |-_{IO} F@i)
      2) If i <= j and C is a table fact or an event or a mess fact of bigger phase as F then there exists k such that T |-_{IO} F@k and k < j
      3) If i < j and C is a mess fact of same phase as F then there exists k such that T |-_{IO} F@k and k < j
      4) If C is an attacker fact or C is a mess fact of same phase as F with i = j then there exists k such that 
          T |-_{IO} F@k but we cannot deduce anything else about k.

    We therefore consider the following invariant on the lemmas considered during the saturation (i.e. 
    elements of type [lemma]):
      For all [(F,qrel)] in the conclusion of a lemma:
        - F must be variable-safe
        - if [qrel = QOMax (sem,ord)] with [sem = SemPhaseLess] then 
            - either one of the facts in the premise is an attacker fact
            - or else one of the facts in the premise is a mess fact of same phase as F and ord = Leq
        - if [qrel = QOSpecific ordl] and [(i,(sem,ord))] is an element of [ordl] then :
            - either the i-th fact of the premise is an attacker fact
            - or it is a mess fact of same phase as F and [ord = Leq]

  *)

(** Inclusion functions *)

(** [includes_clause rel1 rel2] return [true] only if [R(rel2) \subseteq R(rel1)]. *)
val includes_clause : clause_ordering_relation -> clause_ordering_relation -> bool

(** [includes_query_clause qrel crel] return [true] only if [R(crel) \subseteq R(qrel)]. *)
val includes_query_clause : query_ordering_relation -> clause_ordering_relation -> bool

(** Similar to [includes_clause]. *)
val includes_query : query_ordering_relation -> query_ordering_relation -> bool

(** Intersection and union functions *)

(** [intersection_clause rel1 rel2] returns a clause ordering relation [rel] such that:
    R(rel) = R(rel1) or  R(rel) = R(rel2)) or R(ord) = R(rel1) \cap R(rel2).
    The first two cases is when we cannot properly express properly the intersection in our formalism. *)
val intersection_clause : clause_ordering_relation -> clause_ordering_relation -> clause_ordering_relation 

(** Similar to [intersection_clause] but on query ordering relations. *)
val intersection_query : query_ordering_relation -> query_ordering_relation -> query_ordering_relation
  
(** [union_clause rel1 rel2] returns a clause ordering relation [rel] such that:
    R(rel1) \cup  R(rel2) \subseteq R(rel)). *)
val union_clause : clause_ordering_relation -> clause_ordering_relation -> clause_ordering_relation

(** [union_clause_list [rel1;...;reln]] returns the union of [rel1],...,[reln]. *)
val union_clause_list : clause_ordering_relation list -> clause_ordering_relation

(** [union_clause_map2 f [a1;...;an] [b1;...;bn]] returns the union of [f a1 b1],...,[f an bn]. *)
val union_clause_map2 : ('a -> 'b -> clause_ordering_relation) -> 'a list -> 'b list -> clause_ordering_relation

(** Similar to [union_clause]. *)
val union_query : query_ordering_relation -> query_ordering_relation -> query_ordering_relation

(** [union_query_list [rel1;...;reln]] returns the union of [rel1],...,[reln]. *)
val union_query_list : query_ordering_relation list -> query_ordering_relation

(** [union_query_map2 f [a1;...;an] [b1;...;bn]] returns the union of [f a1 b1],...,[f an bn]. *)
val union_query_map2 : ('a -> 'b -> query_ordering_relation) -> 'a list -> 'b list -> query_ordering_relation

(** Compose clause relation *)

(** [compose_clause crel1 crel2] compose the two relations [crel1] and [crel2] assuming that [crel1] corresponds
    to a relation with a single conclusion. *)
val compose_clause : clause_ordering_relation -> clause_ordering_relation -> clause_ordering_relation

(** Predicates allowed to be ordered. *)

(** [can_predicate_have_clause_ordering_relation p] returns [true] when [p] is one of the following
- an (bi,inj)event (blocking or not)
- a (bi)attacker (blocking or not)
- a (bi)table (blocking or not)
- a (bi)mess predicate (blocking or not)
- a user-defined predicate (non-blocking only)
*) 
val can_predicate_have_clause_ordering_relation : predicate -> bool

val can_fact_have_clause_ordering_relation : fact -> bool

(** [can_predicate_have_clause_ordering_relation p] returns [true] when [p] is one of the following
- an (bi,inj)event (blocking or not)
- a (bi)attacker (non-blocking only)
- a (bi)mess (non-blocking only)
- a (bi)table (non-blocking only) *)
val can_predicate_have_query_ordering_relation : predicate -> bool

val can_fact_have_query_ordering_relation : fact -> bool

(** [can_hyp_and_concl_be_ordered hyp concl] returns [true] when [hyp] and [concl] can be ordered
    with [hyp] acting as an hypothesis of a clause and [concl] its conclusion. *)
val can_hyp_and_concl_be_ordered : fact -> fact -> bool

(** Some transformations *)

(** [enforce_strict_clause_ordering_relation crel] transforms the relation [crel'] such that:
    if (F@i,[C1@k_1,...,Cn@k_n]) \in R(crel) implies i <= k_j 
    then (F@i,[C1@k_1,...,Cn@k_n]) \in R(crel') implies i < k_j *)
val enforce_strict_clause_ordering_relation : clause_ordering_relation -> clause_ordering_relation
  
(** [create_ordering_with_conclusion i] generates an ordering for the ordering of F_i with itself in 
    F_1 && ... && F_n. *)
val create_ordering_with_conclusion : int -> fact -> clause_ordering_relation

(** Multiset ordering:
  
  We consider the lexicographic ordering on multisets of steps for inductive proofs:
    (MSet_Std,MSet_User)
  where 
    - MSet_Std is the multiset of steps of standard facts 
    - MSet_Std is the multiset of steps of user-defined facts.
  
  Thus if (MSet_Std_prem,MSet_User_prem) are the steps on which we aim to apply an inductive lemma
  and  (MSet_Std_concl,MSet_User_concl) are the steps of the conclusion, we need to show that 
    
    (MSet_Std_prem,MSet_User_prem) < (MSet_Std_concl,MSet_User_concl)
*)

(** [steps_strictly_before crel_list (n_std1,n_user1) (n_std2,n_user2)] returns [true] if for all pairs
    (MSet_Std1,MSet_User1) and (MSet_Std2,MSet_User) satisfying [crel_list], we have:
      (MSet_Std1,MSet_User1) < (MSet_Std2,MSet_User)
    - [n_std1] and [n_std2] indicates the number of standard facts we consider (|MSet_Std1| = n_std1 and |MSet_Std2| = n_std2)
    - [n_user1] and [n_user2] indicates the number of user-defined facts we consider (|MSet_User1| = n_user1 and |MSet_User2| = n_user2)

    The i-th element (from 1) of [crel_list] corresponds to the relation of the i-th element of facts with steps from (MSet_Std1,MSet_User1).
    The [n_std1] first elements of [crel_list] correspond to the facts from MSet_Std1.
    Similarly, in each relation from [crel_list], the indices less than [n_std2] refer to the facts with steps from MSet_Std2.
*)
val steps_strictly_before : clause_ordering_relation list -> (int * int) -> (int * int) -> bool

(** Managing Ordering Data *)

(** [generate_empty_ordering_data ()] creates a fresh empty ordering data. *)
val generate_empty_ordering_data : unit -> ordering_data

(** [are_ordering_proofs_recorded] indicates whether or not the ordering proofs need to be recorded.
    It is typically set to [true] when proving a lemma and [false] otherwise. *)
val are_ordering_proofs_recorded : bool ref

(** [initialise_record rq] needs to be called before proving the query [rq]. *)
val initialise_recording : realquery -> unit

(** [record_proved_ordering ()] needs to be called once a query has been proved within the scope of the [auto_cleanup] *)
val record_proved_ordering : unit -> unit

(** [update_proved_ordering ()] needs to be called once a query has been proved outside of the [auto_cleanup] to 
    definitely record the proved ordering. *)
val update_proved_ordering : unit -> unit

(** [cleanup_proved_ordering_when_not_true ()] is called when an attack on the query is found and it removes the 
    recorded proofs as they are not valid. *) 
val cleanup_proved_ordering_when_not_true : unit -> unit

(** [cleanup_ordering ()] is called before returning the result of the query. When the query is true
    then the recorded proved ordering can be preserved. *) 
val cleanup_ordering : unit -> unit

(** [cleanup_proved_ordering ()] removes the recorded proofs inside a query. When proving a group of lemmas by induction
    with [MaxSubset], a query can have a [True] result that is invalided when the inductive hypotheses are not all
    proved. In such a case, we have to prove again the query which requires to clean the recorded proofs before. *)
val cleanup_proved_ordering : query -> unit

(** Ordering of Axioms, Restrictions and Inductive lemmas *)

(** [assume_proved_realquery rq] considers that the realquery [rq] holds and thus will update the ordering data
  in [rq] with the appropriate ordering proofs. *)
val assume_proved_realquery : realquery -> unit

(** Same as [assume_proved_realquery] but on queries. *)
val assume_proved : query -> unit

(** [refresh_ordering_data state] create new references for proofs in the ordering data
    of the lemmas, axioms, restrictions and queries of [state].
    @warning This function should only be applied on the "initial" state obtained after encoding. 
    It should not be applied between the different proofs of lemmas and queries as it would
    erase previously proved results. *)
val refresh_ordering_data : t_pi_state -> t_pi_state

(** Update the set of events and predicates that need to be resolve again through 
    a second saturation. Updates also wether or not the restrictions implies the need
    to use liveness, i.e. enforce ordered clause during the saturation. *)
val requires_liveness_and_additional_saturation : t_pi_state -> t_pi_state

(** Verification of queries:
    
  After verifying a lemma where we need to record the ordering proofs, we expect the 
  ordering data proofs to be either None or Some ord where ord is inluded by the target
  ordering. The first case can occur with a disjunction \phi1 \vee \phi2 where  \phi1 was
  always proved and never phi2. As such, when we translate the lemma (queyr) as a
  [Types.lemma], we can remove the disjunction that contain a fact with None as proved 
  ordering.
*)

(** [check_lemmas_are_proved lems] checks that the proved ordering of the query are either  
  None or Some ord with ord inluded by the target ordering.*)
val check_lemmas_are_proved : t_lemmas -> unit

(** In [verify_and_update_ordering_data_IO f_next ord_data crel] the query fact with ordering data
    [ord_data] has been instantiated with a matching fact of the hypotheses of the clause with ordering
    relation [crel]. The ordering data [ord_data] is updated if [crel] is included in the target ordering. 
    @raise Unify if the [crel] is not included in the target ordering of [ord_data]. *)
val verify_and_update_ordering_data_IO : (unit -> 'a) -> ordering_data -> clause_ordering_relation -> 'a

(** [update_ordering_data_list_semantics f_next fact_ord_data_l sem] is called after the query facts in 
    [fact_ord_data_l] are proved with the semantics [sem]. The function updates the proofs of the 
    ordering data with the relation corresponding to [sem] semantics.
    @warning All the target orderings in [fact_ord_data_l] must be the same. 
    @warning [sem] must be either [SemPhaseless] or [SemStd]*)  
val update_ordering_data_list_semantics : (unit -> 'a) -> (fact * ordering_data) list -> clause_ordering_relation option -> satisfaction_semantics -> 'a

(** Debugging *)

module Debug :
sig
  val display_query_order : query_order -> unit

  val display_query_ordering_relation : query_ordering_relation -> unit

  val display_clause_ordering_relation : clause_ordering_relation -> unit

  val display_ordering_data : ordering_data -> unit
end
