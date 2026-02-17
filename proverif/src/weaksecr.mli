open Types
open Clause

val initialize : t_solver_kind -> unit

module type WeakSecrSig =
sig
  type clause

  (** [is_standard_clause r] returns true when the clause [r] 
      must be preserved from transformations *)
  val is_standard_clause : clause -> bool
  val simplify : (clause -> unit) -> (clause -> unit) -> clause -> unit
  val selfun : clause -> int
  val remove_equiv_events : (clause -> unit) -> clause -> unit

end

module Std : WeakSecrSig with type clause = Std.clause
module Ord : WeakSecrSig with type clause = Ord.clause