(** Module dealing with Lemmas and Axioms *)

open Types
open Pitypes

(* [valid_lemma] checks that the query satisfies the conditions to be a lemma:
   Internally, a lemma is a correspondence query F1 && ... && Fn ==> \psi such that:
    - \psi does not contain nested query or injective event. 
    - facts in \psi may ordered with respect to fact of the premises.
    - Attacker facts should not be asked to be proved < than an attacker fact of the premise.
        --> ProVerif would never be able to prove such ordering.
        --> This is the case for all queries (not only lemmas), so this point is checked
            in [Encode_queries.encode_temporal_realquery_e], not in [valid_lemma].
    - If the lemma is for equivalence use, it should not require occurrence variables
      (because it will be translated using the predicate event2 which has no occurrence).

   In an input file, we will prevent syntactically nested queries or injective events. We 
   allow temporal variables. Note that a query with temporal variables will be encoded into
   a query with possibly nested queries and ordered facts. Hence, only lemmas that can 
   be encoded into a valid internal lemma will be accepted.*)
val valid_lemma : bool -> t_one_lemma -> unit

(* The function [organize_lemmas pi_st] records which lemmas correspond to an axiom or restriction.
   It also removes lemmas that are not applied due to application options.
*)
val organize_lemmas : t_pi_state -> t_pi_state

(* The function [verify_conditions_query] checks that the conclusion
   is determined by the terms in the premise even in the presence of
   an equational theory. *)
val verify_conditions_query : query_e -> unit

(* The function [generate_inductive_lemmas pi_st] considers the query
   of [pi_st] and simplifies it to see if it can be proved by induction.

   The function [Piauth.simplify_query] must provide a stronger query
   than the simplified queries produced using
   [Lemma.generate_inductive_lemmas], because the proof of the query
   obtained by [Piauth.simplify_query] allows us to apply the
   inductive lemma.
   In particular, we simplify nested queries [e ==> concl] into conjunctions
   [e && concl] in both functions. *)
val generate_inductive_lemmas : t_pi_state -> t_pi_state

val transl_lemmas : t_horn_state -> t_pi_state -> t_horn_state

(* [check_axioms] should be called before encoding of axioms*)
val check_axioms : 'a reduc_state -> (realquery_e * bool) list -> bool

val no_bound_name_t_lemmas : t_lemmas -> bool

(* [encode_lemmas state public_vars ror_opt] encodes the lemmas in [state.pi_lemma].
   More specifically, [state.pi_lemma] should already be translated and any single lemma
   of type [t_one_lemma] should be of the form :
    { ql_query = q; ql_original_query = None; ql_real_or_random = r_opt; ql_index_query_for_induction = None }
   with
    - [q] being a correspondance query possibly with public variables.
    - [r_opt = Some vl] being the query secret vl [real_or_random] associated to this lemma; or None otherwise.
   When the public variables of [q] differ from [public_vars] or when the associated
   query secret real_or_random [r_opt] differ from [ror_opt], the lemma is ignored.
   Invariant: Lemmas that contain [choice] should be associated with query secret real_or_random.
   Other lemmas are transformed into:
    { ql_query = q'; ql_original_query = Some q; ql_real_or_random = r_opt; ql_index_query_for_induction = None }
   where [q'] is the query [q] without public variables. *)
val encode_lemmas : t_pi_state -> term list -> term list option -> t_pi_state

(* [encode_lemmas_for_equivalence_queries state] keeps the lemmas in [state.pi_lemma]
   that are not specified with public variables or for a query secret real_or_random. *)
val encode_lemmas_for_equivalence_queries : t_pi_state -> t_pi_state

(* [translate_to_bi_lemma state] transforms the lemmas into
   bi-lemmas (lemmas using attacker2, mess2, table2 when needed),
   for use with biprocesses. *)
val translate_to_bi_lemma : t_pi_state -> t_pi_state

(* [convert_lemma_for_monoprocess lem] checks whether the bilemma corresponds in fact to
   a lemma on one side of the biprocess. If it is the case, it returns the lemma for the
   corresponding side of the biprocess (ql_application_side is set to LeftSide or RightSide).
   When it is not the case, [lem] is returned.

   Note that technically, a lemma could correspond to both sides of the biprocess.
    ex : lemma event(A(x,y)) ==> event(B(x',y'))
   But in this case, it is sufficient to prove only one side of the lemma. In case
   the lemma would be proved on one side but not on the other, it means the biprocess
   diverges before the premises are triggered and so the lemma would not help anyway in the
   proof of equivalence. *)
val convert_lemma_for_monoprocess : t_one_lemma -> t_one_lemma


module Debug : 
sig
   val check_lemma : lemma -> unit

   val display_lemma : lemma -> unit

   val display_t_lemmas : t_lemmas -> unit
end
