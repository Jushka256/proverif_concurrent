open Types

(** [corresp_initialize horn_state] initializes the state of the solver and
   saturates the set of clauses given in [horn_state].
   It allows subsequent calls to [solving_request_rule], [query_goal_std],
   and [sound_bad_derivable]. *)
val corresp_initialize : t_horn_state -> unit

(* [solving_request_rule clause] performs resolution on the hypothesis of the
   clause [clause], and returns the set of obtained clauses with no
   selected hypothesis. In particular, when it returns no clause,
   the hypothesis of [clause] is not derivable.
   It is called from piauth.ml and from reduction.ml, function
   check_query_falsified, so it comes indirectly from piauth.ml *)
val solving_request_rule : ?close_equation:bool -> Types.lemma list -> Clause.Ord.clause -> Clause.Ord.clause list

(* [query_goal_std fact] performs resolution on [fact], and returns
   the set of obtained clauses with no selected hypothesis that may
   derive [fact]. In particular, when it returns no clause,
   [fact] is not derivable.
   It is called only from reduction.ml, in case LetFilter
   - so it comes indirectly from piauth.ml *)
val query_goal_std : Types.lemma list -> fact -> Clause.Ord.clause list
(* [sound_bad_derivable clauses] returns the set of clauses that
   derive bad from the initial clauses [clauses].
   It is sound, that is, if it returns a clause, then bad is derivable
   from this clause.
   It restores the previous clauses after the call, so that
   calls to [resolve_hyp] or [query_goal_std] can still be made
   on the initial clauses passed to [corresp_initialize] after calling
   [sound_bad_derivable].
   It is called only from piauth.ml *)
val sound_bad_derivable : reduction list -> Clause.Ord.clause list
(* [reset()] resets the whole state *)
val reset : unit -> unit

(* [main_analysis horn_state queries] determines whether the [queries]
   are derivable from the clauses in [horn_state]. It displays the
   results directly on the standard output or in an html file.
   It is called only for the Horn and typed Horn front-ends *)
val main_analysis : t_horn_state -> fact list -> unit

(* [bad_derivable horn_state] determines whether [bad] is derivable
   from the clauses in [horn_state]. It returns the clauses with
   no selected hypothesis that may derive bad.
   It is called from [Main.interference_analysis] *)
val bad_derivable : t_horn_state -> Clause.Ord.clause list

val is_hypothesis_unsatisfiable : Clause.Ord.clause -> bool

val bad_in_saturated_database : unit -> bool

val bad_in_saturated_database_opt : unit -> Clause.Ord.clause option
