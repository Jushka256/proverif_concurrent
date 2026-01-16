open Types

(* This module regroups the different kinds of clauses we consider in the algorithm *)

(* Property of derivation for user-defined predicates:

  A derivation from D from C_user is valid when for all nodes \eta of D, if F_0, \tau_0 is the label 
  of the incoming edge of \eta then :
    If F_0 = G\sigma with G_1 && ... && G_n <==> G declared by the user then
      a. either \eta is labeled by the clause G_1 && ... && G_n -> G, 
      b. or else \eta is not the root and the node \eta' connected to the incoming edge
        of \eta is labeled by a clause G_i -> G

  For homogeneity, if pred(P) is a user-defined predicate then for any trace T, 
  we denote by T, \tau |-  F when \tau is the size of the smallest valid derivation D
  from C_user such that the incoming edge of the root of D is labeled by F
*)

(* Main Origin Invariant of a derivation.
  
  In the saturation procedure, for a derivation on non-ordered clause we have
  the following invariant (extended from Definiton 18 of [BCC22 - Techreport]).

  Let T an IO-compliant trace. Let S_p a set of predicates to prove. We defined the invariant
    InvOrigin(D,T,S_p,C_user)
  when for all nodes \eta of D, if F_0, \tau_0 is the label 
  of the incoming edge of \eta then :

  1. If \eta is labeled by the listen rule then the step \tau_1, \tau_2 of respectively
    the mess and att fact of the outgoing edge satisfy :
      - \tau_1 <= \tau_0
      - if att is in S_p then \tau_2 < \tau_0 else \tau_2 <= \tau_0

  2. If \eta is not the listen rule then for all outgoing edges of \eta labeled F',\tau',
      - if pred(F) and pred(F') are both user-defined predicates or both not user-defined predicates
        then  
          if pred(F') \in S_p then \tau' < \tau_0 else \tau' \leq \tau_0
      - else no condition

  3. If F_0 = att_k(f(M_1,...,M_n)) with f.f_cat = Tuple
      a. either \eta is labeled by the application function clause of f, and 
        if att_k \in S_p then T,\tau_0 |-_{IO} F_0

      b. or else \eta is not the root and the node \eta' connected to the incoming edge
        of \eta is labeled by a projection of f and if att_k \in S_p then T, \tau_0 |-_i F_0
        (notice that it is not the strict satisfaction |-_{IO} but |-_i)

  4. If F_0 = G\sigma with G_1 && ... && G_n <==> G declared by user then
      a. either \eta is labeled by the clause G_1 && ... && G_n -> G, and 
        if pred(F_0) \in S_p then T,0 |-_{IO} F_0
      b. or else \eta is not the root and the node \eta' connected to the incoming edge
        of \eta is labeled by a clause G_i -> G and if pred(F_0) \in S_p then T, 0 |-_i F_0

  5. In any other case, if pred(F_0) \in S_p then T,\tau_0 |-_{IO} F_0  
*)

(* Main Origin Invariant of a derivation on bitrace
  
  We only consider bitraces T such that either T is convergent or else T = C_0 -> ... -> C_{n-1) -> C_n
  and C_0 -> ... -> C_{n-1} is convergent.

  We say that T, \tau |- bad when T is divergent and \tau = |T|.

  We say that T, \tau |-_{IO} input(x,x') when:
    - either T, \tau |-_{IO} att(x,x')
    - or an input in(diff[x,x'],y); P is in the multiset of processes in T[\tau].

  We say that T, \tau |-_{IO} output(x,x') when 
    - either T, \tau |-_{IO} att(x,x')
    - or an outut out(diff[x,x'],u); P is in the multiset of processes in T[\tau]

  Compared to [BCC22 - Techreport], we add the clause 
    att_k(x,x') -> output_k(x,x')   (ROut)
  Moreover, the clauses RIBad1 and RIBad2 are completed with:
    input_k(x,x') && output_k(x,y') && x' <> y' -> bad
    input_k(x,x') && output_k(y,x') && x <> y -> bad
  Finally, the translation of the process additionally generates the clause
      H -> output_k(fst(Nρ),snd(Nρ)) 
  similarly to the input clause.
  
  Thanks to this, we can define the following invariant for the derivation on bitraces:
  
  Let T an IO-compliant bitrace. Let S_p a set of predicates to prove. We define the invariant
    InvOriginB(D,T,S_p,C_user)
  when for all nodes \eta of D, if F_0, \tau_0 is the label of the incoming edge of \eta then :

  1. If \eta is labeled by the listen rule then the step \tau_1, \tau_2 of respectively
    the mess and att fact of the outgoing edge satisfy :
      - \tau_1 <= \tau_0
      - if att is in S_p then \tau_1 < \tau_0 else \tau_1 <= \tau_0

  2. If \eta is labeled by the rule (RIn) or (ROut) then the step \tau_1 labeling
  the outgoing edge of \eta is such that \tau_1 <= \tau_0.

  3. If \eta is labeled by the rules RIBad1', RIBad2', RIBad1, RIBad2 then for all
  outgoing edges of \eta labeled by step \tau_1, we have \tau_1 <= \tau_0

  4. If \eta is not the listen rule then for all outgoing edges of \eta labeled F',\tau',
      - if pred(F) and pred(F') are both user-defined predicates or both not user-defined predicates
        then  
          if pred(F') \in S_p then \tau' < \tau_0 else \tau' \leq \tau_0
      - else no condition

  5. If F_0 = att_k(f(M_1,...,M_n),f(M'_1,...,M'_n)) with f.f_cat = Tuple
      a. either \eta is labeled by the application function clause of f, and 
        if att_k \in S_p then T,\tau_0 |-_{IO} F_0

      b. or else \eta is not the root and the node \eta' connected to the incoming edge
        of \eta is labeled by a projection of f and if att_k \in S_p then T, \tau_0 |-_i F_0
        (notice that it is not the strict satisfaction |-_{IO} but |-_i)

  6. If F_0 = G\sigma with G_1 && ... && G_n <==> G declared by the user then
      a. either \eta is labeled by the clause G_1 && ... && G_n -> G, and 
        if pred(F_0) \in S_p then T,0 |-_{IO} F_0
      b. or else \eta is not the root and the node \eta' connected to the incoming edge
        of \eta is labeled by a clause G_i -> G and if pred(F_0) \in S_p then T, 0 |-_i F_0

  7. In any other case, if pred(F_0) \in S_p then T,\tau_0 |-_{IO} F_0.

  Note that this invariant integrates user-defined predicates with equivalence proofs. It is not yet
  integrated in the tool but that will be the invariant for when it is the case.
*)

module type HypSig =
sig
  type hyp

  (* Creates a dummy hypothesis *)
  val dummy : hyp

  (** Access *)

  (** [get_fact h] returns the fact inside [h]. *)
  val get_fact : hyp -> fact

  (** [get_ordering_relation h] returns the ordering relation inside [h]. *)
  val get_ordering_relation : hyp -> clause_ordering_relation

  (** Generation *)

  (** [merge h1 h2] merges the two hypotheses [h1] and [h2] that have the same fact 
      into a single hypothesis.
      @warning [h1] and [h2] are assumed to have the same fact. The function does not verify it. *)
  val merge : hyp -> hyp -> hyp

  (** [create_strictly_before f h] creates an hypothesis from the fact [f] which
      occurs strictly before [h]. 
      - If the predicate of [f] is not a predicate that is required to be proved,
        then the function returns an hypothesis that occurs before [h] but not strictly. 
      - If the predicate of [f] is not allowed to have an ordering, then no ordering is given. *)
  val create_strictly_before : fact -> hyp -> hyp

  (** [create_list_strictly_before fl h] returns the same result as [List.map (fun f -> create_strictly_before f h) fl] 
      but it is more efficient. *)
  val create_list_strictly_before : fact list -> hyp -> hyp list

  (** [create_no_ordering_allowed f] creates an hypothesis with no ordering. Note that
     the fact should not be allowed to be ordered. Otherwise, the hypothesis needs to be created
     with another generation function (e.g. : [create_strictly_before]).
     @exit when [f] can be ordered. *)
  val create_no_ordering_allowed : fact -> hyp

  (** [create_from_composition hyp_solved hyp_unsolved] creates an hypothesis corresponding to the 
      composition of two hypotheses where the relation of [hyp_solved] is with respect to [hyp_unsolved] whose
      relation is with respect to some conclusion C. The result is the hypothesis with the fact of [hyp_solved] and whose
      relation is with respect to C. *)
  val create_from_composition : hyp -> hyp -> hyp

  (** When the premise of a nested query is matched with an hypothesis [hyp], we need to generate
    a clause where the fact of [hyp] has been added to the conclusion in order to prove the conclusion of
    the nested query. The function [create_nested_hypothesis hyp size_orig_concl n] creates the hypothesis with the fact
    corresponding to the conclusion added. As we will add possibly several nested premises in the conclusion
    [n] indicates that [hyp] is the [n]-th nested conclusion added and [size_orig_conc] is the size of 
    the original conclusion (before nested hypotheses were added). *)
  val create_nested_hypothesis_nth_conclusion : hyp -> int -> int -> hyp

  (** Create Hypothesis from the application of a lemma

        Consider:
          - F in the conclusion of the lemma (occuring @i in the trace)
          - G_p in the hypothesis of the clause that is matched with the p-th premise of the lemma (occuring @j in the trace)
          - C_q in the q-th conclusion of the clause (occuring @k in the trace)

        We denote by COrdRel_p the clause ordering relation on G_p.

        We say that F is variable-safe if all its variables are in an event, message or table fact in
        the premises of the lemma.

        We want to determine the [clause_ordering_relation] that links F@i and C_q@k.
        Note that we know that T |-_{IO} G_p@j and T |-_{IO} C_q@k.
        Let us assume that j Rel1 k with Rel1 \in { <; <= } (all relation are always in { <; <= }).

        We basically want to see what we can deduce from a situation where
          i Rel1 j Rel2 k

        Recall that for table predicate, T |-{IO} table(tbl(M))@i phase k holds either when tbl(M) has
        been inserted at step i in phase k, or if it was already inserted in previous phase and i is the
        step where the phase changed. 

        Let us denote by CompRel(i,Rel1,p,Rel2,q) that can returns <, <=, or bot to indicate that 
        following the below conditions, we can determine that if CompRel(i,Rel1,p,Rel2,q) <> bot then 
            \exists i'. T |-{IO} F@i' and i' CompRel(i,Rel1,p,Rel2,q) k.
          
        1) If T |-_{IO} F@i
          then 
            if < \in { Rel1,Rel2 } then CompRel(i,Rel1,p,Rel2,q) = <
            else CompRel(i,Rel1,p,Rel2,q) = <=

        2) If T |-_{p} F@i then it means that F is an attacker fact of phase n.
          If F is not variable-safe
          then then CompRel(i,Rel1,p,Rel2,q) = bot
          else 
            - if (Rel1 = < or G_p is an event or G_p is a table fact with phase 0) and 
                if 
                  either G_p is not an attacker fact, 
                  or (C_q is attacker fact of phase m) implies m > n 
                then CompRel(i,Rel1,p,Rel2,q) = <
                else CompRel(i,Rel1,p,Rel2,q) = bot
            - else 
                - if C_q is an attacker/mess/table fact of phase m > n then CompRel(i,Rel1,p,Rel2,q) = <
                - else if C_q is a mess/table fact of phase n and and Rel2 = < then CompRel(i,Rel1,p,Rel2,q) = <
                - else if C_q is an event then CompRel(i,Rel1,p,Rel2,q) = <
                - else CompRel(i,Rel1,p,Rel2,q) = bot

        3) If F@i and T |-_{i} F@i then CompRel(i,Rel1,p,Rel2,q) = bot
          
        Note that we can avoid variable-safety check by ensuring that when the lemma is proved, if the fact
        is not variable-safe then we only indicate a _{i} semantics.

        Now let us look at the clause ordering relation on G_p.  We define CompRelG(i,Rel1,p) such that:
          - if COrdRel_p = CONone then CompRelG(i,Rel1,p) = CONone
          - if COrdRel_p = COMax Rel then
              if for all k, CompRel(i,Rel1,p,Rel,k) = < then CompRelG(i,Rel1,p) = COMax <
              else if for all k, CompRel(i,Rel1,p,Rel,k) <> bot then CompRelG(i,Rel1,p) = COMax <=
              else CompRelG(i,Rel1,p) = CONone

          - if COrdRel_p = COrdRel spec_list then
              CompRelG(i,Rel1,p) = COSpecific spec_list' where spec_list is build by replacing each
              entry (k,Rel) by (k,CompRel(i,Rel1,p,Rel,q)) when <> bot and remove it otherwise 

        The final determination of the clause ordering relation on F@i is computed as follows
          if relation of F@i is QOSpecific [j_r,Rel_r]_r then you can do the intersection of CompRelG(i,Rel_r,j_r) for all r.
          if relation of F@i is QOMax Rel then you do the union of the intersection of all CompRelG(i,Rel,j) for all j
          if relation of F@i is QONone then CONone
      *)

  (** In [create_from_lemma_application pred_concl_list matched_hyp], the lists:
    - [pred_concl_list] is the list of predicates of the conclusion
    - [matched_hyp] corresponds to how the premise of the lemma was matched in a reverse order
      For example, for a lemma F1 && ... && Fn ==> psi
      the argument [matched_hyp] will be the list [(i_n,Fn);...;(i_1,F1)] where the indices
      i_1,...,i_n are the index in the rules.
  The call returns a function [create : fact -> query_ordering_relation -> hyp option].
  When calling [create f qrel], [f] is the fact in the conclusion of the lemma and [qrel] is its query ordering
  relation. The function returns the hypothesis to be added in the clause if it is possible. *)
  val create_from_lemma_application : predicate list -> (int * hyp) list -> (fact -> query_ordering_relation -> hyp option)

  (** [create_hypothesis_from_nth_conclusion n f] creates an hypothesis from [f] assuming that [f] is the [n]-th fact
      from the conclusion. *)
  val create_hypothesis_from_nth_conclusion : int -> fact -> hyp

  (** [create_hypotheses_from_conclusion f] creates the hypotheses corresponding from the conclusion [f]. Note that 
      [f] corresponds to the full conclusion, i.e. may be a combined fact. *)
  val create_hypotheses_from_conclusion : fact -> hyp list

  (** Testing *)

  (** [equal_fact h1 h2] returns [true] iff the facts of [h1] and [h2] are equal (ignores the links) *)
  val equal_facts : hyp -> hyp -> bool

  (** [is_strictly_before_conclusion h] returns [true] iff the hypothesis [h] occurs strictly before the conlusion.
      If [f] is an hypothesis that is not allowed to be ordered, the function returns [false]. 
      @warning Should only be applied when the conclusion is a single fact, in [Rules.elim_taut]. *)
  val is_strictly_before_conclusion : hyp -> bool

  (** [can_ignore_nounif h] returns [true] iff the hypothesis can ignore a nounif declaration. *)
  val can_ignore_nounif : hyp -> bool

  (** [decrease_ignore_nounif_authorization h] reduces strictly the authorization of [h]
    to ignore a nounif. 
    @warning the function should only be applied on an hypothesis that can ignore nounif, i.e. when [can_ignore_nounif = true]. *)
  val decrease_ignore_nounif_authorization : hyp -> hyp

  (** Matching *)

  (** [match_ordering_for_redundant_hyp h1 h2] checks that the ordering [h1] matches the ordering of [h2]
      for the application of the [redundant_hyp] simplification rule. 
      @raise NoMatch when the check fails. *)
  val match_ordering_for_redundant_hyp : hyp -> hyp -> unit

  (** [match_hyp h1 h2] matches [h1] with [h2].
      @raise NoMatch if they cannot be matched. *)
  val match_hyp : hyp -> hyp -> unit

  (** Tools *)

  (** [map_fact f_map hyp] replaces the fact [f] in [hyp] by [f_map f] *)
  val map_fact : (fact -> fact) -> hyp -> hyp

  (** [iter_term f h] applies [f] on the arguments of the fact in [h]. *)
  val iter_term : (term -> unit) -> hyp -> unit

  (** Copies *)

  (** [copy h] copies [h] by refreshing the variables. 
      @warning only [VLink _] are allowed in [h] 
      @warning no cleanup of variables *)
  val copy : hyp -> hyp

  (** [copy2 h] copies [h] by refreshing the variables and going recursively through the links [TLink _]. 
      @warning only [TLink _] and [VLink _] are allowed in [h] 
      @warning no cleanup of variables *)
  val copy2 : hyp -> hyp

  (** [copy3 h] follows through the variables with [TLink _] once. Does not refresh the
      variables. *)
  val copy3 : hyp -> hyp

  (** [copy4 h] recursively follows through the variables with [TLink _]. Does not refresh the
      variables. *)
  val copy4 : hyp -> hyp

  (** Display *)

  (** [display h] displays the hypothesis [h] without cleanup of the display renaming. *)
  val display : hyp -> unit

  (** [display h] displays the hypothesis [h] and cleanup the display renaming. *)
  val display_indep : hyp -> unit
end

(** The module of the hypothesis for the standard saturation procedure.*)
module Hyp : HypSig with type hyp = fact

(** The module of the hypothesis for the ordered saturation procedure. The integer correspond to the ignore nounif *)
module HypOrd : HypSig with type hyp = fact * clause_ordering_relation * int

module type ClauseSig =
sig
  type hyp

  type clause = 
    {
      hypotheses : hyp list;
      conclusion : fact;
      history : history;
      constraints : constraints
    }

  (** The empty clause *)
  val empty : clause

  (** Tools *)

  (** [iter_term f cl] applies [f] on all the terms in the clause [cl]. *)
  val iter_term : (term -> unit) -> clause -> unit

  (** [iter_term_exclude_constraint f cl] applies [f] on all the terms in the clause [cl] 
      except for the ones on [cl.constraints]. *)
  val iter_term_exclude_constraint : (term -> unit) -> clause -> unit

  (** Application of inductive lemmas *)

  (** [allow_conclusion_for_induction cl] returns [true] when the conclusion of [cl] can be used
      to apply an inductive lemma. *)
  val allow_conclusion_for_induction : clause -> bool

  (** [is_inductive_lemma_application lem cl matched_hyp] returns [true] if the application of 
      the inductive lemma with matching premise [matched_hyp] is strictly before the inductive 
      hypothesis.
      
      [matched_hyp] corresponds to how the premise of the lemma was matched in a reverse order
      For example, for a lemma F1 && ... && Fn ==> psi
      the argument [matched_hyp] will be the list [(i_n,Fn);...;(i_1,F1)] where the indices
      i_1,...,i_n are the index in the rules.*)
  val is_inductive_lemma_applicable : lemma -> clause -> (int * hyp) list -> bool

  (** [is_lemma_applicable_for_equivalence cl matched_hyp] returns [true] if the application of
      the lemma with matching premise [matching_hyp] is sure to be applied on a convergent bitrace. *)
  val is_lemma_applicable_for_equivalence : clause -> (int * hyp) list -> bool

  (** Copies *)

  (** [copy cl] copies [cl] by refreshing the variables. 
      @warning only [VLink _] are allowed in [cl] 
      @warning no cleanup of variables *)
  val copy : clause -> clause

  (** [copy2 cl] copies [cl] by refreshing the variables and going recursively through the links [TLink _]. 
      @warning only [TLink _] and [VLink _] are allowed in [cl] 
      @warning no cleanup of variables *)
  val copy2 : clause -> clause

  (** [copy3 cl] follows through the variables with [TLink _] once. Does not refresh the
      variables. *)
  val copy3 : clause -> clause

  (** [copy4 cl] recursively follows through the variables with [TLink _]. Does not refresh the
      variables. *)
  val copy4 : clause -> clause

  (** Others *)

  (** [reduction_of cl] transforms the clause [cl] into a reduction hence losing all additional information *)
  val reduction_of : clause -> reduction

  (** [of_reduction r] transforms the reduction [r] into a clause without any ordering information. 
      This function should be used with care.  *)
  val of_reduction : reduction -> clause

  (** Display *)

  module type DisplaySig =
  sig
    (** [display cl] displays the clause [cl] without cleanup of the display renaming. *)
    val display : clause -> unit

    (** [display cl] displays the clause [cl] and cleanup the display renaming. *)
    val display_indep : clause -> unit

    val display_nonewline : clause -> unit

    val display_abbrev : clause -> unit
  end

  module Text : DisplaySig
  module Html : DisplaySig

end

module Std : ClauseSig with type hyp = Hyp.hyp
module Ord : ClauseSig with type hyp = HypOrd.hyp

(** [clauseOrd_of_saturated_clause cl] transforms the standard clause [cl] into an ordered clause with the 
    ordering information corresponding to the invariant InvOrigin. *)
val clauseOrd_of_saturated_clause : Std.clause -> Ord.clause

(** [clauseOrd_of_saturated_clause_no_order cl] transforms the standard clause [cl] into an ordered clause but
    loses all ordering information. This is useful when the query does not request to prove any ordering.  *)
val clauseOrd_of_saturated_clause_no_order : Std.clause -> Ord.clause

