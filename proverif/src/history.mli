open Types
open Clause

(** Tools *)

val iter_term_history : (term -> unit) -> history -> unit

(** Generation *)

val get_rule_hist : rulespec -> history

val build_fact_tree : history -> fact_tree

val get_clause_from_derivation : fact_tree -> reduction

val change_type_attacker : predicate -> typet -> predicate

type recheck_t = (Ord.clause -> bool) option

(* [build_history recheck clause] builds a derivation for the clause
   [clause] using the history stored in that clause.
   When the depth or number of hypotheses of clauses is bounded,
   it may in fact return a derivation for an instance of [clause].
   In this case, it uses [recheck] to verify that the obtained
   clause still contradicts the desired security property.
   Raises [Not_found] in case of failure *)
val build_history : recheck_t -> Ord.clause -> fact_tree

(* [unify_derivation recheck tree] implements a heuristic
   to find traces more often, especially with complex protocols:
   it unifies rules of the derivation [tree] when possible.
   It returns the obtained derivation.
   Note that success is not guaranteed; however, when the heuristic fails,
   the derivation does not correspond to a trace.

This heuristic can break inequality constraints.
We recheck them after modifying the derivation tree.
We also recheck that the derivation still contradicts the security
property after unification, using the function [recheck].

When the heuristic fails or these checks fail, we return the
initial derivation [tree]. 

No link should be active when this function is called.
It creates links when it modifies the derivation. *)
val unify_derivation : (fact_tree -> 'a) -> recheck_t -> fact_tree -> 'a

(* For debugging only
val verify_clause_and_derivation : reduction -> unit *)
