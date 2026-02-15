open Types
open Clause

val never_select_weight : int
val weight_of_user_weight : nounif_value -> int

(* Replaces [FAny x] with [FVar x] when there is an [FVar x] elsewhere
   in the format. This is how the format is understood. *)
val homogeneous_format : ?id_thread:int -> fact_format -> fact_format

val initialize : ?id_thread:int -> (fact_format * nounif_value * nounif_op) list -> t_solver_kind -> unit

(* [exists_ignored_nounif ()] returns [true] if and only if some nounif have been
   declared with the option [ignoreAFewTimes]. *)
val exists_ignored_nounif : unit -> bool

module type SelfunSig =
sig
  type clause
  type queue

  (** Initialisation of the selection function after generation of the clauses. The function
      will go through the queue and detect initial nounif declarations to be added. *)
  val initialize_before_saturation : ?id_thread:int -> queue -> unit

  (** The standard selection function. [selection_fun cl] will return the position of the hypothesis
      in the clause that will be selected. It returns [-1] when no hypothesis are selected. 
      The function may automatically declare some nounif statement when needed. *)
  val selection_fun : ?id_thread:int -> clause -> int

  (** Similar to [selection_fun] except that the automatic detection of nounif has been deactivated. *)
  val selection_fun_nostatechange : ?id_thread:int -> clause -> int

  (** [selection_fun_ignore_nounif cl] checks whether one hypothesis of [cl] can be 
      matched with a nounif declared with option [ignoreAFewTimes]. When it is the case,
      the function returns the position of the hypothesis selected as well as the updated
      clause. When no hypothesis is authorized, the function returns -1 and the outputted
      clause is physically the same as [cl]. *)
  val selection_fun_ignore_nounif : ?id_thread:int -> clause -> int * clause
end

module Std : SelfunSig with type clause = Std.clause and type queue = Database.QueueClause.t
module Ord : SelfunSig with type clause = Ord.clause and type queue = Database.QueueOrdClause.t
