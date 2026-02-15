(* This module optimizes subsumption using feature vectors.
   See Simple and Efficient Clause Subsumption with Feature Vector Indexing,
   by Stephan Schulz, in: Automated Reasoning and Mathematics,
   LNCS, volume 7788, Springer. *)

open Types
open Pitypes
open Clause
open Concurrent

(* Subsumption *)

module type SubsumptionSig =
  sig
    type hyp
    type clause

    type subsumption_data =
      {
        (** For an element (s,hfact) in the lists, [s] is the size of the fact of [hfact]. *)
        bound_facts : (int * hyp) list; (** List are always kept in decreasing order w.r.t. the first projection of the pair *)
        unbound_facts : (int * hyp) list (** List are always kept in decreasing order w.r.t. the first projection of the pair *)
      }

    type sub_annot_clause = clause * subsumption_data

    val empty_sub_data : subsumption_data
    val empty_sub_annot_clause : sub_annot_clause

   (* In the following functions, a clause can always be seen as its reduction part and its subsumption data part.
      For instance, when a clause is an ordered_reduction, the subsumption data contains the ordering function of the clause.

      For example, on a reduction R = (H && \phi -> C), the subsumption data [sub_data] of R is such that:
        - [sub_data.bound_facts] is the list of facts in H (with their size) that contains only variables of C
        - [sub_data.unbound_facts] are the remaining facts of H (with their size). Hence all facts in [sub_data.unbound_facts]
          contain a variable not in C.

      When R is an ordered reduction, it's similar except that [sub_data.bound_facts] and [sub_data.unbound_facts] also contain
      the ordering functions associated to the ordered facts in H.

      As mentioned above, [sub_data.bound_facts] and [sub_data.unbound_facts] are sorted by decreasing size.
    *)

    (** [implies r1 r2] returns true iff the rule [r1] implies/subsumes the rule [r2],
       where [r1] and [r2] are clauses with associated subsumption data. *)
    val implies : sub_annot_clause -> sub_annot_clause -> bool

    (** [implies_redundant r1 r2] returns a pair of booleans [(r_implies,block_set_implies)]
       where [r_implies] is true when [r1] implies/subsumes [r2]
       and [block_set_implies] is true when the blocking predicates part [Hblock1] of
       [r1 = Hblock1 && Hother1 -> C1] "subsumes" that part [Hblock2] of
       [r2 = Hblock2 && Hother2 -> C2], i.e. there exists a substitution [sigma] such that
       [sigma C1 = C2] and [sigma Hblock1 \subseteq Hblock2] for set inclusion.
       (When [block_set_implies] is false, subsumption cannot become true
       after future resolutions so we can cut this branch when we determine
       whether a clause is redundant.) *)
    val implies_redundant : sub_annot_clause -> sub_annot_clause -> bool * bool

    (** Similar to [implies] except that we do not apply an initial test on the number of hypotheses in the rule.
       This function is only used in combination with the feature vector. *)
    val implies_no_test : clause -> subsumption_data -> clause -> subsumption_data -> bool

    val implies_no_test_concurrent : ?id_thread:int -> token -> clause -> subsumption_data -> clause -> subsumption_data -> bool

    (** [generate_subsumption_data r] generates the subsumption data associated to [r]. *)
    val generate_subsumption_data : clause -> sub_annot_clause

    (** [implies_mod_eq_set cl1 cl2] returns [true] when [cl1] set-subsumes [cl2] modulo 
        the equational theory. 
        @warning The function is not complete. It may return [false] despite the set-subsumption holding.*)
    val implies_mod_eq_set : clause -> clause -> bool

  end

module SubClause : SubsumptionSig with type clause = Std.clause and type hyp = Hyp.hyp
module SubOrdClause : SubsumptionSig with type clause = Ord.clause and type hyp = HypOrd.hyp

(* Features *)

type feature

(* We will always assume that a feature_vector is always ordered increasingly
   using the lexicographic order. *)
type feature_vector = (feature * int) list

val compare_feature : feature -> feature -> int

(* Recording *)

val record_fun : funsymb -> unit
val record_name : funsymb -> unit
val record_predicate : predicate -> unit
val record_from_fact : fact -> unit
val record_from_rule : reduction -> unit

(* Display *)

val display_feature : feature -> string
val display_feature_vector : feature_vector -> unit

(* Generation of feature vector *)

module type FeatureGenerationSig =
  sig
    type subsumption_data
    type clause
    type annot_clause = clause * feature_vector * subsumption_data

    (* [initialize ()] needs to be executed before starting saturating clauses. *)
    val initialize : unit -> unit

    val generate_feature_vector_and_subsumption_data : clause -> annot_clause
  end

module FeatureGenClause : FeatureGenerationSig with type subsumption_data = SubClause.subsumption_data and type clause = Std.clause
module FeatureGenOrdClause : FeatureGenerationSig with type subsumption_data = SubOrdClause.subsumption_data and type clause = Ord.clause

(* Set of clauses *)

module type SetSig =
  sig
    type hyp
    type clause
    type subsumption_data
    type sub_annot_clause = clause * subsumption_data
    type annot_clause = clause * feature_vector * subsumption_data

    type active_status = Active | Inactive | Removed

    type 'a element =
      {
        mutable annot_clause: sub_annot_clause;
        mutable selected_fact: hyp option;
        mutable additional_data : 'a;
          (* When the clause has a selected hypothesis, it will store its index.
             When the clause has its conclusion selected, it will store whether
	     all hypotheses of the clause are unselectable. *)
        mutable active : active_status;
      }

    type 'a t

    (* The empty set *)
    val create : unit -> 'a t

    (* Should not be applied on an element that is already active. *)
    val activate : 'a t -> 'a element -> unit

    (* Should not be applied on an element that is already inactive. *)
    val deactivate : 'a t -> 'a element -> unit

    (* [add set annot_cl uni_fact add_data] adds to [set] the annotated clause [cl].
       (An annotated clause is a clause with associated feature vector
       and subsumption data.)
       [uni_fact] is the selected fact of [cl]. When [uni_fact = None] then it refers
       to the conclusion of [cl] otherwise it refers to an hypothesis of [cl].
       Note that [cl] is active in the resulting set. *)
    val add : 'a t -> annot_clause -> hyp option -> 'a -> unit

    (* [implies set annot_cl] checks whether an active clause from [set] implies
       the annotated clause [cl]. *)
    val implies : 'a t -> annot_clause -> bool

    (* [deactivate_implied_by empty_add_data set annot_cl] deactivates the clauses from [set]
       that are implied by the annotated clause [annot_cl].
       [empty_add_data] is a empty additional data value, that replaces the additional
       data of deactivated clauses. *)
    val deactivate_implied_by : 'a -> 'a t -> annot_clause -> unit

    (* [cleanup_deactivated set] removes the deactivated clauses in [set] *)
    val cleanup_deactivated : 'a t -> unit

    (* [iter f set] applies [f] to all active clauses *)
    val iter : ('a element -> unit) -> 'a t -> unit

    (* [iter_unifiable f set fact] applies [f] to all active clauses in [set]
       whose selected fact may be unifiable with [fact] *)
    val iter_unifiable : ('a element -> unit) -> 'a t -> fact -> unit

    (* [length set] returns the number of active clauses in [set]. *)
    val length : 'a t -> int

    (* [to_list set] returns the list of active clauses in [set]. *)
    val to_list : 'a t -> clause list

    (* [exists f set] returns [true] if there exists an active clause [cl] in [set]
       such that [f cl = true]. *)
    val exists : (clause -> bool) -> 'a t -> bool
  end

module SetClause : SetSig with type hyp = Hyp.hyp and type clause = Std.clause and type subsumption_data = SubClause.subsumption_data
module SetOrdClause : SetSig with type hyp = HypOrd.hyp and type clause = Ord.clause and type subsumption_data = SubOrdClause.subsumption_data

(* Queue of clauses *)

module type QueueSig =
  sig

    type clause
    type subsumption_data
    type annot_clause = clause * feature_vector * subsumption_data
    type t

    (* Generate a new queue *)
    val new_queue : unit -> t

    (* [add q annot_cl] adds to the queue [q] the annotated clause [cl] *)
    val add : t -> annot_clause -> unit

    (* [get q] takes the first clause of the queue with its respective feature
      vector and implication data. Note that the resulting clause is always activated. *)
    val get : t -> annot_clause option

    (* [implies q annot_cl] checks whether an active clause from [q] implies the
       annotated clause [cl]. *)
    val implies : t -> annot_clause -> bool

    (* [deactivate_implied_by q annot_cl] deactivates the clauses from [q]
       that are implied by the annotated clause [cl] *)
    val deactivate_implied_by : t -> annot_clause -> unit

    (* [cleanup_deactivated q] removes the deactivated clauses in [q]. *)
    val cleanup_deactivated : t -> unit

    (* [iter f q] applies [f] on each active clause of the queue [q]. *)
    val iter : (annot_clause -> unit) -> t -> unit

    (* [length q] returns the number of clauses in [q]. *)
    val length : t -> int
  end

module QueueClause : QueueSig with type clause = Std.clause and type subsumption_data = SubClause.subsumption_data
module QueueOrdClause : QueueSig with type clause = Ord.clause and type subsumption_data = SubOrdClause.subsumption_data

(* Database *)

module type DBSig =
  sig
    type clause
    type queue
    type 'a set

    type t =
      {
        queue : queue;
        mutable count : int;
        mutable base_ns : bool set;
        mutable base_sel : int set;
      }

    val check_no_link : t -> unit

    val create : unit -> t

    (* [simplify_hypotheses] simplifies a clause by removing some of its
       hypotheses, so that the obtained clause subsumes the original one.
       In practice, we remove attacker facts containing ground public terms
       (including attackerBin and attackerGuess)  *)
    val simplify_hypotheses : clause -> clause

    val add_rule : t -> clause -> unit

    val display_initial_queue : t -> unit

    val display_rule_during_completion : t -> (clause * int) -> unit

    val display_dynamic_statistics : t -> unit
  end

module DB : DBSig with type clause = Std.clause and type queue = QueueClause.t and type 'a set = 'a SetClause.t
module DBOrd : DBSig with type clause = Ord.clause and type queue = QueueOrdClause.t and type 'a set = 'a SetOrdClause.t

(* Set of saturated clauses
   This is a specific module for saturated clause. It is typically a subset of functions from SetClause
   where we only need to work with unification *)

module SetSatClause :
  sig
    (* The type of set of saturated clause *)
    type t

    (* The empty set *)
    val empty : t

    (* [of_list sat_rules] generates a set of saturated clauses from the list [sat_rules] *)
    val of_list : Ord.clause list -> t

    (* [iter_unifiable f set fact] apply [f] on all saturated clauses in [set]
       whose conclusion may be unifiable with [fact] *)
    val iter_unifiable : (Ord.clause -> unit) -> t -> fact -> unit

    val iter : (Ord.clause -> unit) -> t -> unit
  end
