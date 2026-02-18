(* This module contains basic functions to manipulate terms modulo
   an equational theory *)

open Types
open Clause

(* returns true when at least one equation has been registered *)
val hasEquations : unit -> bool

val hasConvergentEquations : unit -> bool

(* Transforms equations into rewrite rules on constructors
   When !Param.html_output is set, an HTML file must be open to receive
   the display. *)
val record_eqs : t_horn_state -> unit

val collect_unset_vars : binder list ref -> term -> unit

(* Close clauses modulo the equational theory *
 close_rule_eq is used for clauses entered by the user in Horn-clause
 front-ends,
 close_fact_eq is used for closing the goals *)
val close_term_eq : (term -> unit) -> term -> unit
val close_term_list_eq : (term list -> unit) -> term list -> unit
val close_fact_eq : (fact -> unit) -> fact -> unit

module type EqSig =
sig
  type clause

  val close_modulo_eq : (clause -> unit) -> clause -> unit
  val close_hyp_modulo_eq : (clause -> unit) -> clause -> unit
end

module Std : EqSig with type clause = Std.clause
module Ord : EqSig with type clause = Ord.clause

(* Close terms by rewrite rules of constructors and destructors. *)
val close_term_destr_eq : constraints -> (constraints -> term -> unit) -> term -> unit

(* Close clauses by rewrite rules of constructors and destructors. *
   Used for clauses that define predicates (for LetFilter). *)
val close_rule_destr_eq : (fact list * fact * constraints -> unit) -> fact list * fact * constraints -> unit

(* [f_has_no_eq f] returns [true] when the function symbol [f]
   has no equation. *)
val f_has_no_eq : funsymb -> bool

(* Unification modulo the equational theory *)
val close_term_eq_synt : (term -> 'a) -> term -> 'a
val close_constraints_eq_synt : (constraints -> 'a) -> constraints -> 'a
val unify_modulo : (unit -> 'a) -> term -> term -> 'a
val unify_modulo_list : (unit -> 'a) -> term list -> term list -> 'a

val unify_modulo_save : (unit -> 'a) -> term -> term -> 'a
val unify_modulo_list_save : (unit -> 'a) -> term list -> term list -> 'a

val copy_remove_syntactic : term -> term
val copy_remove_syntactic_fact : fact -> fact
val copy_remove_syntactic_conclusion_query : Pitypes.conclusion_query -> Pitypes.conclusion_query
val copy_remove_syntactic_realquery : Pitypes.realquery -> Pitypes.realquery
val remove_syntactic_term : term -> term
val remove_syntactic_fact : fact -> fact
val remove_syntactic_constra : constraints -> constraints
val remove_syntactic_rule : reduction -> reduction

(* [gather_nat_vars constra] returns the list of natural number variables
   in [constra] *)
val gather_nat_vars : constraints -> binder list

(* Treatment of inequality constraints *)

(* Remove inequalities of the form x <> caught-fail as they are always true in
  the generated clauses.*)
val remove_caught_fail : constraints -> constraints

exception FalseConstraint

(* [check_constraints constra] checks that the constraints [constra]
   are still satisfiable. It raises [FalseConstraint] when they are not. *)
val check_constraints : constraints -> unit

(* [check_closed_constraints constra] checks that the constraints [constra]
   are still satisfiable. Returns [true] when they are.
   Assumes that the constraints are closed.
   Used to evaluate destructors in trace reconstruction. *)
val check_closed_constraints : constraints -> bool

(* Simplification of constraints *)

(** [simplify_constraints_simple get_vars_op c] simplifies the constraints [c].
  When [get_vars_op = None], all variables in [c] are preserved.
  When [get_vars_op = Some f], the variables of [f ()] are preserved. 
  @raise FalseConstraint when the constraint is false *)
val simplify_constraints_simple : (unit -> binder list) option -> constraints -> constraints

(** [simplify_constraints_continuation get_vars_op f_next f_inst c] simplifies the constraints [c]
  and calls [f_next] on the simplified constraints when no variables have been instantiated
  otherwise it calls [f_inst] on the simplified constraints.
  @alert When [f_inst] is called, some variables are linked.
  Note that there is only one call to either [f_next] or [f_inst].

  When [get_vars_op = None], all variables in [c] are preserved.
  When [get_vars_op = Some f], the variables of [f ()] are preserved. 

  @raise FalseConstraint when the constraint is false *)
val simplify_constraints_continuation : (unit -> binder list) option -> (constraints -> 'a) -> (constraints -> 'a) -> constraints -> 'a

(** [simplify_constraints_optimal get_vars_op f_next f_inst c] simplifies the constraints [c].
  It may apply some case distinction in the presence of inequalities.
  Calls [f_next] on a simplified constraint when no variables have been instantiated
  Calls [f_inst] on a simplified constraint whith instantiated variables.
  No function is called when the constraint is not satisfiable.
  @alert When [f_inst] is called, some variables are linked.

  When [get_vars_op = None], all variables in [c] are preserved.
  When [get_vars_op = Some f], the variables of [f ()] are preserved. 
*)
val simplify_constraints_optimal : (unit -> binder list) option -> (constraints -> unit) -> (constraints -> unit) -> constraints -> unit

(** Implication of constraints *)

(* [implies_constraints get_vars_op constraint1 constraint2]
  checks that the constraints [constraint1] imply the constraints [constraint2].
  It returns true when the check succeeds and false when it fails.
  [constraint2] is supposed to contain links that come from a previous matching.
   
  When [get_vars_op = None], all variables in [constraint1] and [constraint2] are preserved.
  When [get_vars_op = Some f], the variables of [f ()] are preserved. 

  These functions differ by how they copy the constraint [constraint2]:
  - [implies_constraints] makes no copy.
  - [implies_constraints3] uses [Terms.copy_constra3], so it copies
    one level of links: it is suitable after matching.
  - [implies_constraints4] uses [Terms.copy_constra4], so it copies
    links recursively. *)

val implies_constraints : (unit -> binder list) option -> constraints -> constraints -> bool
val implies_constraints3 : ?id_thread:int -> (unit -> binder list) option -> constraints -> constraints -> bool
val implies_constraints4 : (unit -> binder list) option -> constraints -> constraints -> bool

(* [get_solution f_next constra] calls [f_next] after linking variables to
   a solution of the constraints [constra].
   Raises [FalseConstraint] when there is no solution. *)
val get_solution : (unit -> 'a) -> constraints -> 'a

(* Transforms equations into rewrite rules on constructors, also closing
   the rewrite rules of destructors modulo equations.
   When !Param.html_output is set, an HTML file must be open to receive
   the display. *)
val record_eqs_with_destr : Pitypes.t_pi_state -> unit

(* Simplifies a term using the equations *)
exception Reduces
val simp_eq : term -> unit
