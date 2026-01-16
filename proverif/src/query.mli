open Types
open Pitypes 

(** Properties of correspondence queries:

  A correspondence query given as input must satisfy the following properties:
    - Premise of a nested query can only be a single (inj-)event
    - Comparisons between two attacker facts can only be a non-strict inequality (i.e. <=)
        -> This is due to the fact that ProVerif would never be able to prove a strict ordering
        with the |-_i semantics.
    - For queries on bitraces, comparisons between event time variables should not be with = or <>.
    - Premise cannot contain QEq, QMax, QGr or QMaxq
    - Premise cannot contain inequalities or disequalities impacting time variables.

  Each inputted query is encoded into another correspondence query that satisfies the following properties:
    - The query should not contain any time variable
    - Events of the premise are ordered as follows:
        1. Injective events
        2. events 
        3. standard predicates (attacker,mess,table)
        4. user-defined predicates
        5. nested Events
        6. inequalities, disequalities, is_nat
        7. subterms
    - If an event in the premise of the query does not require occurrence, then the same event in the
    conclusion of the query should also not require occurrence.

*)

(** [count_std_and_user_facts rq] returns [(nb_std,nb_user)] where [nb_std] is the number of standard
    fact in the premise of [rq] and [nb_user] is the number facts with user-defined predicates. Note that
    it does not count subterms predicate as standard nor user-defined. 
    @warning [rq] must satisfy the invariant on how facts are sorted in the premise of a query. 
    @warning We assume here that there are no nested fact in the premise. *)
val count_std_and_user_facts : realquery -> int * int

(** The following functions consider queries after encoding. *)

(** [map_term_realquery f rq] replaces all terms [t] in [rq] by [f t]. *)
val map_term_realquery : (term -> term) -> realquery -> realquery

(** [number_of_facts_in_premise evl] counts the number of facts in [evl] assuming that [evl] is the
    premise of a query. It excludes subterm facts. *)
val number_of_facts_in_premise : event list -> int

module Debug :
sig
  val display_query : query -> unit

  val display_t_query : t_query -> unit
end
