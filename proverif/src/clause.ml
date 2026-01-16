open Types

(* This module regroups the different kinds of clauses we consider in the algorithm *)

module type HypSig =
sig
  type hyp

  (* Creates a dummy hypothesis *)
  val dummy : hyp

  (** Access *)

  (** [get_fact h] returns the fact inside [h] *)
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
      @warning Should only be applied when the conclusion is a single fact. *)
  val is_strictly_before_conclusion : hyp -> bool

  (** [can_ignore_nounif h] returns [true] iff the hypothesis can ignore a nounif declaration. *)
  val can_ignore_nounif : hyp -> bool

  (** [decrease_ignore_nounif_authorization h] reduces strictly the authorization of [h]
    to ignore a nounif. In particular, 
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

module Hyp : HypSig with type hyp = fact =
struct

  type hyp = fact

  let dummy = Param.dummy_fact
  
  let get_fact x = x [@@inline]

  let get_ordering_relation x =
    if Ordering.can_fact_have_clause_ordering_relation x
    then COSpecific [1,Less]
    else CONone
    [@@inline]

  let merge x _ = x [@@inline]
  let create_strictly_before x _ = x [@@inline]
  let create_list_strictly_before fl _ = fl [@@inline]
  let create_no_ordering_allowed f = 
    if Ordering.can_fact_have_clause_ordering_relation f 
    then Parsing_helper.internal_error __POS__ "[Hyp.create_no_ordering_allowed] The hypothesis should not be allowed to be ordered.";
    f 
    [@@inline]

  let create_hypotheses_from_conclusion = Terms.fact_list_of_conclusion
  let create_hypothesis_from_nth_conclusion _ f = f [@@inline]

  let create_from_composition h1 _ = h1 [@@inline]

  let create_nested_hypothesis_nth_conclusion h _ _ = h [@@inline]

  let equal_facts = Terms.equal_facts

  let is_strictly_before_conclusion fact = 
    Ordering.can_fact_have_clause_ordering_relation fact &&
    Ordering.is_pred_to_prove_fact (Terms.unblock_predicate_fact fact)
      (* In principle, this function should use the same ordering as the one given by
	 [clauseOrd_of_saturated_clause].
	 However, [is_strictly_before_conclusion] is called only in [Rules.elim_taut],
	 so the clause Rl is not concerned, it is not possible that the conclusion is not user-defined
	 and the hypothesis is user-defined, so [Ordering.can_fact_have_clause_ordering_relation]
	 yields the same result as [Ordering.can_hyp_and_concl_be_ordered],
	 and [Ordering.is_pred_to_prove_fact fact] will in fact always be true because
	 blocking facts in the hypothesis of a clause that correspond to a non-blocking fact
	 in the conclusion are added by a lemma, and therefore they are in [pred_to_prove].
	 We check it for safety. *)
      [@ppwarning "Ideally, do exactly the same checks as in [clauseOrd_of_saturated_clause]."]
      
  let can_ignore_nounif _ = false [@@inline]
  let decrease_ignore_nounif_authorization x = x [@@inline]
  let match_ordering_for_redundant_hyp _ _ = () [@@inline]

  let match_hyp = Terms.match_facts 

  let map_fact f x = f x [@@inline]

  let iter_term f = function
    | Pred(_,args) -> List.iter f args

  let copy = Terms.copy_fact
  let copy2 = Terms.copy_fact2
  let copy3 = Terms.copy_fact3
  let copy4 = Terms.copy_fact4
  let display = Display.Text.display_fact
  let display_indep x = Display.auto_cleanup_display (fun () -> Display.Text.display_fact x)

  type status_fact =
    | OtherFact
    | MessFactSamePhase
    | AttackerFact

  let create_from_lemma_application pred_concl_list matched_hyp =
    let are_all_strict = List.for_all (fun (i,_) -> i >= 0 ) matched_hyp in 

    let get_status phase_lem_concl p = match (Terms.unblock_predicate p).p_info with
      | Attacker _ | AttackerBin _ -> AttackerFact
      | Mess(n,_) | MessBin(n,_) ->
          if n = phase_lem_concl 
          then MessFactSamePhase
          else 
            if n > phase_lem_concl
            then OtherFact
            else Parsing_helper.internal_error __POS__ 
              ("Get status should only be called when the fact in the conclusion of the lemma occur before its premise with phaseless semantics.\n"^
              "Its phase thus cannot be bigger than the one of the premise")
      | _ -> OtherFact
    in

    let get_phase_fact (Pred(p,_)) = match (Terms.unblock_predicate p).p_info with
      | Attacker(n,_) | AttackerBin(n,_) -> n
      | _ -> Parsing_helper.internal_error __POS__ "This function should only be used in the PhaseLess case. Hence, by invariant on lemma, we should have that the fact is an attacker fact."
    in

    (* When [fact] does not allow an ordering, the [qrel] should be [QONone] which does not imply
       strictly before the conclusion even though we can add it in the hypothesis. We therefore
       make it a special case. *)
    fun fact qrel ->
      let can_be_added =
        if Ordering.can_fact_have_clause_ordering_relation fact
        then 
          match qrel with
          | QONone -> false
          | QOMax (SemIO,Less) -> true
          | QOMax (SemIO,Leq) -> are_all_strict
          | QOMax (SemPhaseLess,ord) -> 
              let phase = get_phase_fact fact in
              List.for_all (function p -> match get_status phase p with
                | OtherFact -> true
                | MessFactSamePhase when ord = Less -> true
                | _ -> false
              ) pred_concl_list
          | QOMax _ -> false
          | QOSpecific ord_fun_spec -> 
              let rec go_through i ord_l concl_list = match ord_l,concl_list with
                | [],_ -> false
                | (k,_)::_, _::q_concl when i < k -> go_through (i+1) ord_l q_concl
                | (_,(SemIO, _))::_, _ -> true
                | (_,(SemPhaseLess,ord))::q_ord_rel, p::q_concl ->
                    begin match get_status (get_phase_fact fact) p with
                    | OtherFact -> true
                    | MessFactSamePhase when ord = Less -> true
                    | _ -> go_through (i+1) q_ord_rel q_concl
                    end
                | _::q_ord_rel, _::q_concl -> go_through (i+1) q_ord_rel q_concl
                | _, [] -> Parsing_helper.internal_error __POS__ "[create_from_lemma_application] Unexpected list structure"
              in
              go_through 1 ord_fun_spec pred_concl_list 
        else true
      in
      if can_be_added 
      then Some fact
      else None

end

module HypOrd : HypSig with type hyp = fact * clause_ordering_relation * int =
struct
  type hyp = fact * clause_ordering_relation * int

  let dummy = (Param.dummy_fact,CONone,0)

  let get_fact (f,_,_) = f [@@inline]
  let get_ordering_relation (_,rel,_) = rel [@@inline]
  let merge (f,ord1,n1) (_,ord2,n2) = (f,Ordering.intersection_clause ord1 ord2,min n1 n2) [@@inline]

  let create_strictly_before f (f',ord,n) =
    if Ordering.is_pred_to_prove_fact f
    then (f,ord,n)
    else (f,Ordering.enforce_strict_clause_ordering_relation ord,n)
    [@@inline]

  let create_list_strictly_before fl (f',ord,n) =
    let ord' = 
      if Ordering.is_pred_to_prove_fact f'
      then ord
      else Ordering.enforce_strict_clause_ordering_relation ord
    in
    List.map (fun f -> (f,ord',n)) fl
    [@@inline]

  let create_no_ordering_allowed f =
    if Ordering.can_fact_have_clause_ordering_relation f 
    then Parsing_helper.internal_error __POS__ "[Hyp.create_no_ordering_allowed] The hypothesis should not be allowed to be ordered.";
    (f,CONone,0)
    [@@inline]

  let create_from_composition (f1,crel1,_) (_,crel2,n) = (f1,Ordering.compose_clause crel1 crel2,n) [@@inline]

  let create_nested_hypothesis_nth_conclusion (f,crel,_) size_orig_concl n = 
    let f' = match f with
      | Pred(p,[ev;occ]) when p == Param.inj_event_pred_block -> Pred(Param.inj_event_pred,[ev;occ])
      | Pred(p,args) when p == Param.event_pred_block -> Pred(Param.event_pred,args)
      | _ -> Parsing_helper.internal_error __POS__ "[HypOrd.create_nested_hypothesis_nth_conclusion] Premise of a nested query should only be events. "
    in
    let crel' = match crel with
      | COSpecific l -> COSpecific (l@[n+size_orig_concl,Leq])
      | _ -> COSpecific ([n+size_orig_concl,Leq])
    in

    (f',crel',!Param.initial_nb_of_nounif_ignore)

  let create f rel = f,rel,0 [@@inline]

  let create_hypotheses_from_conclusion f = 
    (* All fact in the conclusion can always have an ordering function *)
    let f_l = Terms.fact_list_of_conclusion f in
    List.mapi (fun i f ->
      (f,COSpecific [i+1,Leq],!Param.initial_nb_of_nounif_ignore) 
    ) f_l

  let create_hypothesis_from_nth_conclusion n f = 
    (* All fact in the conclusion can always have an ordering function *)
    (f,COSpecific [n,Leq],!Param.initial_nb_of_nounif_ignore)
    [@@inline]

  let equal_facts (f1,_,_) (f2,_,_) = Terms.equal_facts f1 f2 [@@inline]

  let is_strictly_before_conclusion (_,ord,_) = ord = COSpecific [(1,Less)] [@@inline]
    (* We don't need to test here if the fact can have an ordering function since, if it was the case
       then it would have CONone as order. *)

  let can_ignore_nounif (_,_,n) = n > 0 [@@inline]
  let decrease_ignore_nounif_authorization (f,ord,h) = (f,ord,h-1) [@@inline]

  let match_ordering_for_redundant_hyp (f1,ord1,_) (f2,ord2,_) = match f1, f2 with
    | Pred(p1,args1), Pred(p2,args2) ->
      (* This function called only when Pred(p2,args2) is an instance of Pred(p1,args1) *)
        assert(p1 == p2);
        if 
          not (List.for_all2  Terms.equal_terms args1 args2) &&
          not (Ordering.includes_clause ord1 ord2)
        then raise Terms.NoMatch

  let match_hyp (f1,crel1,_) (f2,crel2,_) =
    Terms.match_facts f1 f2;
    if not (Ordering.includes_clause crel1 crel2)
    then raise Terms.NoMatch

  let map_fact f_map (f,ord,n) = (f_map f,ord,n) [@@inline]

  let iter_term f (Pred(_,args),_,_) =  List.iter f args [@@inline]

  type status_fact =
    | OtherFact
    | MessFactSamePhase
    | AttackerFact

  let create_from_lemma_application pred_concl_list matched_hyp =

    let get_status phase_lem_concl p = match (Terms.unblock_predicate p).p_info with
      | Attacker _ | AttackerBin _ -> AttackerFact
      | Mess(n,_) | MessBin(n,_) ->
          if n = phase_lem_concl 
          then MessFactSamePhase
          else 
            if n > phase_lem_concl
            then OtherFact
            else Parsing_helper.internal_error __POS__ 
              ("Get status should only be called when the fact in the conclusion of the lemma occur before its premise with phaseless semantics.\n"^
              "Its phase thus cannot be bigger than the one of the premise")
      | _ -> OtherFact
    in

    (* List of ordering relation corresponding of the matched premises (in order) *)
    let (crel_prem_list,prem_list) = 
      List.fold_left (fun (acc_crel,acc_pred) (_,(Pred(p,_),crel,_)) -> 
        crel :: acc_crel, (p::acc_pred)
      ) ([],[]) matched_hyp
    in 

    let get_phase_fact (Pred(p,_)) = match (Terms.unblock_predicate p).p_info with
      | Attacker(n,_) | AttackerBin(n,_) -> n
      | _ -> Parsing_helper.internal_error __POS__ "This function should only be used in the PhaseLess case. Hence, by invariant on lemma, we should have that the fact is an attacker fact."
    in

    (* By taking the union of relation, we know that if the union relation implies a constraint, then all the relations
      of the premise satisfy this constraint. For example, if the union relation implies "< k_j" then for all 
      r, j_r < k_j. *)
    let union_crel_premise = lazy (Ordering.union_clause_list crel_prem_list) in

    let compute_when_phaseless phase_lem_concl ord_phaseless crel_prem pred_prem  = match get_status phase_lem_concl pred_prem with
      | OtherFact -> Ordering.enforce_strict_clause_ordering_relation crel_prem
      | MessFactSamePhase when ord_phaseless = Less -> Ordering.enforce_strict_clause_ordering_relation crel_prem
      | _ -> 
          match crel_prem with
            | CONone -> CONone
            | COMax ord -> 
                if 
                  List.exists (fun p -> match get_status phase_lem_concl p with
                    | AttackerFact -> true
                    | MessFactSamePhase when ord = Leq -> true
                    | _ -> false
                  ) pred_concl_list
                then CONone
                else COMax Less 
            | COSpecific crel_l ->
                let rec go_through i ord_l pred_concl_list  = match ord_l, pred_concl_list with
                  | [], _ -> []
                  | (k,_)::_, _::q_concl when i < k -> go_through (i+1) ord_l q_concl
                  | (k,ord)::q_ord, p_concl::q_concl ->
                      begin match get_status phase_lem_concl p_concl with 
                      | OtherFact -> (k,Less) :: (go_through (i+1) q_ord q_concl)
                      | MessFactSamePhase when ord = Less -> (k,Less) :: (go_through (i+1) q_ord q_concl)
                      | _ -> go_through (i+1) q_ord q_concl
                      end
                  | _, [] -> Parsing_helper.internal_error __POS__ "Unexpected list structure."
                in
                let crel_l' = go_through 1 crel_l pred_concl_list in
                if crel_l' = []
                then CONone
                else COSpecific crel_l'
    in

    (* A function that given an query ordering relation of the conclusion of a lemma, returns the ordering function that
      will be assigned to the fact added in the hypothesis of the rule *)
    fun fact qrel -> 
      let new_crel = match qrel with
        | QONone | QOMax (SemStd,_) -> CONone
        | QOMax (SemIO,Leq) -> Lazy.force union_crel_premise
        | QOMax (SemIO,Less) -> Ordering.enforce_strict_clause_ordering_relation (Lazy.force union_crel_premise)
        | QOMax (SemPhaseLess,ord) ->
            let phase = get_phase_fact fact in
            Ordering.union_clause_map2 (compute_when_phaseless phase ord) crel_prem_list prem_list
        | QOSpecific q_ord_list ->
            let rec go_through acc i q_ord_list crel_prem_list pred_prem_list = match q_ord_list,crel_prem_list,pred_prem_list with
              | [], _, _ -> acc
              | (k,_)::_, _::q_crel_l, _::q_pred_l when i < k -> go_through acc (i+1) q_ord_list q_crel_l q_pred_l
              | (k,crel_lem)::q_crel_lem_l, prem_crel::q_crel_l, prem_pred::q_pred_l ->
                  let c_ord = match crel_lem with
                    | SemIO, Less -> Ordering.enforce_strict_clause_ordering_relation prem_crel
                    | SemIO, Leq -> prem_crel
                    | (SemPhaseLess,ord) -> compute_when_phaseless (get_phase_fact fact) ord prem_crel prem_pred 
                    | _ -> CONone
                  in
                  go_through (Ordering.intersection_clause acc c_ord) (i+1) q_crel_lem_l q_crel_l q_pred_l
              | _, [], _
              | _, _, [] -> Parsing_helper.internal_error __POS__ "The lists [crel_prem_list] and [pred_prem_list] should have the same size and larger than [q_ord_list]."
            in
            go_through CONone 1 q_ord_list crel_prem_list prem_list
      in
      Some (create fact new_crel)

  let copy (f,ord,n) = (Terms.copy_fact f,ord,n) [@@inline]
  let copy2 (f,ord,n) = (Terms.copy_fact2 f, ord,n) [@@inline]
  let copy3 (f,ord,n) = (Terms.copy_fact3 f, ord,n) [@@inline]
  let copy4 (f,ord,n) = (Terms.copy_fact4 f, ord,n) [@@inline]
  let display (f,_,_) = Display.Text.display_fact f
  let display_indep (f,_,_) = Display.auto_cleanup_display (fun () -> Display.Text.display_fact f)
end

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
  val is_inductive_lemma_applicable: lemma -> clause -> (int * hyp) list -> bool
  
  (** [is_lemma_applicable_for_equivalence cl matched_hyp] returns [true] if the application of
      the lemma with matching premise [matching_hyp] is sure to be applied on a convergent bitrace. *)
  val is_lemma_applicable_for_equivalence : clause -> (int * hyp) list -> bool

  (** Copies *)

  (** [copy cl] copies [cl] by refreshing the variables. 
      @warning only [VLink _] are allowed in [cl] 
      @warning no cleanup of variables *)
  val copy : clause -> clause

  (** [copy2 cl] copies [cl] by refreshing the variables and go recursively through the links [TLink _]. 
      @warning only [TLink _] and [VLink _] are allowed in [cl] 
      @warning no cleanup of variables *)
  val copy2 : clause -> clause

  (** [copy3 cl] follows through the variables with [TLink _] one. Does not refresh the
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

module MakeClause (H:HypSig) =
struct
  type hyp = H.hyp

  type clause = 
    {
      hypotheses : hyp list;
      conclusion : fact;
      history : history;
      constraints : constraints
    }

  let empty =
    {
      hypotheses = [];
      conclusion = Param.dummy_fact;
      history = Empty(Param.dummy_fact);
      constraints = Terms.true_constraints
    }

  (** Tools *)

  let iter_term f cl =
    List.iter (H.iter_term f) cl.hypotheses;
    let Pred(_,args) = cl.conclusion in
    List.iter f args;
    Terms.iter_constraints f cl.constraints

  let iter_term_exclude_constraint f cl =
    List.iter (H.iter_term f) cl.hypotheses;
    let Pred(_,args) = cl.conclusion in
    List.iter f args

  (** Other *)

  let reduction_of cl = 
    List.map H.get_fact cl.hypotheses, cl.conclusion, cl.history, cl.constraints

  (** Copies*)

  let copy cl =
    { cl with
      hypotheses = List.map H.copy cl.hypotheses;
      conclusion = Terms.copy_fact cl.conclusion;
      constraints = Terms.copy_constra cl.constraints
    }

  let copy2 cl =
    { cl with
      hypotheses = List.map H.copy2 cl.hypotheses;
      conclusion = Terms.copy_fact2 cl.conclusion;
      constraints = Terms.copy_constra2 cl.constraints
    }

  let copy3 cl =
    { cl with
      hypotheses = List.map H.copy3 cl.hypotheses;
      conclusion = Terms.copy_fact3 cl.conclusion;
      constraints = Terms.copy_constra3 cl.constraints
    }

  let copy4 cl =
    { cl with
      hypotheses = List.map H.copy4 cl.hypotheses;
      conclusion = Terms.copy_fact4 cl.conclusion;
      constraints = Terms.copy_constra4 cl.constraints
    }

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
end

module Std : ClauseSig with type hyp = Hyp.hyp = 
struct
  include MakeClause(Hyp)

  let of_reduction (hypl,concl,hist,constra) =
    {
      hypotheses = hypl;
      conclusion = concl;
      history = hist;
      constraints = constra
    }

  (** Application of inductive lemmas *)

  let allow_conclusion_for_induction _ = false [@@inline]

  let is_inductive_lemma_applicable _ _ _ = true [@@inline]

  let is_lemma_applicable_for_equivalence _ matched_prem = 
    (* Since we don't have ordering information, we don't allow attacker, mess, input and output fact *)
    List.for_all (fun (_,hyp) -> match Terms.unblock_predicate_fact hyp with
      | Pred({ p_info = AttackerBin _ | MessBin _ | InputPBin _ | OutputPBin _ },_) -> false
      | _ -> true
    ) matched_prem

  (** Display *)

  module Text =
  struct
    let display cl = Display.Text.display_rule (reduction_of cl)
    let display_indep cl = Display.Text.display_rule_indep (reduction_of cl)
    let display_nonewline cl = Display.Text.display_rule_nonewline (reduction_of cl)
    let display_abbrev cl = Display.Text.display_rule_abbrev (reduction_of cl)
  end

  module Html =
  struct
    let display cl = Display.Html.display_rule (reduction_of cl)
    let display_indep cl = Display.Html.display_rule_indep (reduction_of cl)
    let display_nonewline cl = Display.Html.display_rule_nonewline (reduction_of cl)
    let display_abbrev cl = Display.Html.display_rule_abbrev (reduction_of cl)
  end
end

module Ord : ClauseSig with type hyp = HypOrd.hyp =
struct
  include MakeClause(HypOrd)

  let of_reduction (hypl,concl,hist,constra) =
    {
      hypotheses = List.map (fun f -> (f,CONone,0)) hypl;
      conclusion = concl;
      history = hist;
      constraints = constra
    }

  (** Display *)

  let transform_rule cl =
    let (hypl,order_data) =
      List.fold_right (fun hyp (acc_h,acc_ord) ->
        (HypOrd.get_fact hyp::acc_h,(HypOrd.get_ordering_relation hyp,0)::acc_ord)
      ) cl.hypotheses ([],[])
    in
    {
      rule = (hypl,cl.conclusion,cl.history,cl.constraints);
      order_data = order_data
    }

  module Text =
  struct
    let display cl = Display.Text.display_ordered_rule (transform_rule cl)
    let display_indep cl = Display.Text.display_ordered_rule_indep (transform_rule cl)
    let display_nonewline = display
    let display_abbrev cl = Display.Text.display_ordered_rule_abbrev (transform_rule cl)
  end

  module Html =
  struct
    let display cl = Display.Html.display_ordered_rule (transform_rule cl)
    let display_indep cl = Display.Html.display_ordered_rule_indep (transform_rule cl)
    let display_nonewline = display
    let display_abbrev cl = Display.Html.display_ordered_rule_abbrev (transform_rule cl)
  end

  (** Application of inductive lemmas *)

  let allow_conclusion_for_induction _ = true [@@inline]
      (* Useful in case the conclusion combines several facts.
         One may decrease strictly in the multiset ordering even if some premises
	 of the lemma are matched using the conclusion. *)

  let is_inductive_lemma_applicable lem cl matched_hyp = 
    let crel_list = List.rev_map (fun (_,hyp) -> HypOrd.get_ordering_relation hyp) matched_hyp in
    let (nb_std_cl,nb_user_cl) = match cl.conclusion with
      | Pred({p_info = Combined(n1,n2,_);_},_) -> n1,n2
      | Pred({p_info = UserPred _ ; _},_) -> 0,1
      | _ -> 1,0
    in 
    Ordering.steps_strictly_before crel_list (lem.l_nb_std_fact,lem.l_nb_user_fact) (nb_std_cl,nb_user_cl)

  let is_lemma_applicable_for_equivalence cl matched_prem = 
    let concl_in_convergent = match cl.conclusion with
      | Pred({ p_info = AttackerBin _ | MessBin _ | InputPBin _ | OutputPBin _ },_) -> false
      | Pred(p,_) -> p != Param.bad_pred
    in

    concl_in_convergent || List.for_all (fun (_,(_,ord,_)) -> ord = COSpecific [1,Less]) matched_prem

end

(* We need to transform a standard clause into an ordered clause for both equivalence and reachability.
   We forbid right now noninterf, weak secr, and other special queries to rely on lemmas, axioms, and
   restrictions. The invariant would need to be updated to have them.
   Since the clauses are saturated, all the clauses with bad as conclusion are handled in the general case. *)
let clauseOrd_of_saturated_clause cl = 
  let hypl = match cl.Std.history, cl.Std.hypotheses with
    | Rule(_,Rl _,_,_,_), [mess_fact;att_fact] ->  [(mess_fact,COSpecific [1,Leq],0);(att_fact,COSpecific [1,Less],0)]
    | _ ->
        List.map (fun fact -> 
          if Ordering.can_hyp_and_concl_be_ordered fact cl.Std.conclusion
          then
            if Ordering.is_pred_to_prove_fact (Terms.unblock_predicate_fact fact)
            then (fact,COSpecific [1,Less],0)
            else (fact,COSpecific [1,Leq],0)
          else (fact,CONone,0)
        ) cl.Std.hypotheses
  in
  { 
    Ord.hypotheses = hypl;
    Ord.conclusion = cl.Std.conclusion;
    Ord.history = cl.Std.history;
    Ord.constraints = cl.Std.constraints
  }
  
let clauseOrd_of_saturated_clause_no_order cl = 
  let hypl =  List.map (fun fact -> (fact,CONone,0)) cl.Std.hypotheses in
  { 
    Ord.hypotheses = hypl;
    Ord.conclusion = cl.Std.conclusion;
    Ord.history = cl.Std.history;
    Ord.constraints = cl.Std.constraints
  }
