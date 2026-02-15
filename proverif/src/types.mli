(* Types module declares types of the abstract syntax
   tree and of sets of messages.
   There are recursive dependencies between these types,
   that is why they are included in the same module
*)

open Stringmap

type occurrence = { occ : int; precise : bool }

(* Types *)

type typet = { tname : string } [@@unboxed]

(* Information for predicates *)

(* For user-defined predicates *)
type user_pred_spec =
  | Polym of string * int(*value of p_prop*) * typet list
	 (* Polymorphic: declared with at least one argument of type any_type
	    In fact defines a family of predicates, one for each type. 
	    Especially useful when we want to decompose tuples on arguments of the predicate,
	    because we need to generate the predicate at a different type. *)
  | Monom (* Monomorphic: single type *)

(* The integer argument corresponds to the phase of the predicate *)
type info =
    Attacker of int * typet
  | Mess of int * typet
  | InputP of int
  | OutputP of int
  | AttackerBin of int * typet
  | MessBin of int * typet
  | InputPBin of int
  | OutputPBin of int
  | AttackerGuess of typet
  | Compromise of typet
  | Equal of typet
  | Table of int
  | TableBin of int
  | TestUnifP of typet
  | UserPred of user_pred_spec
  | Combined of 
      int (** Number of original standard predicates, without added nested ones *) * 
      int (** Number of original user-defined predicates, without added nested ones *) * 
      predicate list (** List of predicates combined *)
  | Subterm of typet * typet
  | OtherInternalPred (* Corresponds to Events, Bad and dummy predicates *)
  | Block of predicate

and predicate =
  { p_name: string;
    p_type: typet list;
		p_prop: int;
		p_info: info;
    mutable p_record : int (* default = 0 ; otherwise corresponds to the [f_record]th symbol recorded *)
  }

type when_include =
    Always
  | IfQueryNeedsIt

type eq_info =
    EqNoInfo
  | EqConvergent
  | EqLinear

(* Identifiers that can be renamed *)

type renamable_id = {
    orig_name : string; (* Original name in the input file.
                           Empty string if there is no original name.
                           When not empty, [orig_name] is used for display
                           if it is not already used for another identifier in
                           the same scope. *)
    name : string; (* Prefix of the name, to be kept during renaming.
                      Often the [orig_name] after removing an _nnn suffix if any *)
    idx : int; (* Index to be modified when renaming.
                  [name]_[idx] provides a unique name for that identifier.
                  [name] and [idx] are not used much now:
                  They provide a unique identifier for debugging purposes,
                  but they are not used for normal display. *)
    mutable display : string option (* The identifier as it is displayed.
                                       Several identifiers may be displayed with the same
                                       string in different scopes *)
  }

(* Some function symbols have a fixed name (constructors, destructors,
   free names in the typed front-end, ...)
   and some can be renamed (bound names, general variables, the symbol "any_val", ...).
   The type [fixed_or_renamable] allows to handle these two cases. *)

type fixed_or_renamable =
    Fixed of string
  | Renamable of renamable_id

(* Variables *)

type binder = { vname : renamable_id;
                unfailing : bool;
		btype : typet;
		mutable link : linktype array }

(* Processes: patterns *)

and pattern =
    PatVar of binder
  | PatTuple of funsymb * pattern list
  | PatEqual of term

(* What can be linked from variables *)

and linktype =
    NoLink
  | VLink of binder
  | TLink of term
  | CLink of term option array
  | TLink2 of term (* used only in reduction.ml *)
  | FLink of format (* used only in syntax.ml *)
  | PGLink of (unit -> term) (* used only in pisyntax.ml and pitsyntax.ml *)
  | SLink of int (* used only in reduction.ml *)
  | ETLink of enriched_term (* used only in pitsyntax.ml *)
  | Marked

(* Meaning of arguments of names *)

and arg_meaning =
    MUnknown
  | MSid of int (* The argument represents a session identifier *)
  | MCompSid
  | MAttSid
  | MVar of binder * string option
	(* The argument represents a variable.
	   The string option is [Some x] when the argument can be
	   designated by the string [x] in "new a[x = ....]" *)

and name_info = { mutable prev_inputs : term option;
		  mutable prev_inputs_meaning : arg_meaning list }

and funcats =
    Red of rewrite_rules
  | Eq of (term list * term) list
  | Tuple
  | Name of name_info
  | SpecVar of binder
  | Syntactic of funsymb
  | General_var
  | General_mayfail_var
  | Choice
  | ChoiceFst
  | ChoiceSnd
  | Failure

(* The following constraints represents the constraints that can occur in a clause,
  namely disequalties between terms, inequalities between natural numbers and
  predicates testing wheter a term is a natural number or not. *)
and constraints =
  {
    neq : (term * term) list list; (* A list of pair of term represents a disjunction of disequalities.
      [neq l] represents a conjunction of disjunctions of disequalities.
      TRUE can be represented by the list [].
      FALSE can be represented by any list that contains [].*)
    is_nat : term list; (* A list of terms that should be natural number. *)
    is_not_nat : term list; (* A list of terms that should not be natural number. *)
    geq : (term * int * term) list  (* [geq l] represents a conjunction of inequalities where each triple
      [(t,n,t')] in [l] means t + n >= t' *)
  }

and rewrite_rule = term list * term * constraints

and rewrite_rules = rewrite_rule list

(* Function symbols *)

and funsymb = { f_name : fixed_or_renamable;
		mutable f_type : typet list * typet; (* type of the arguments, type of the result *)
		mutable f_cat : funcats;
		f_initial_cat : funcats; (* Used to memorize f_cat before closing using the
                                            equational theory. The initial f_cat is used in reduction.ml,
					    and also in check_several_types *)
		f_private : bool; (* true when the function cannot be applied by the adversary *)
		f_options : int;
                mutable f_record : int (* A distinct integer for each function symbol.
					  Positive when the symbol is used in features for the
					  subsumption test, negative otherwise. *)
              }

(* Terms *)

and term =
    Var of binder
  | FunApp of funsymb * term list

(* Format, to represent facts with jokers *)

and format =
    FVar of binder
  | FFunApp of funsymb * format list
  | FAny of binder

and fact_format = predicate * format list

and fact =
    Pred of predicate * term list

(* Enriched terms, with new, let, if, event, let...suchthat, insert, get *)

and enriched_term =
    { et_desc : enriched_desc;
      et_simple : bool;
      et_simple_no_let : bool;
      et_simple_no_restr : bool;
      et_type : typet;
      et_ext : Parsing_helper.extent }

and enriched_desc =
  | ET_Var of binder
  | ET_FunApp of funsymb * enriched_term list
  | ET_Restr of funsymb * new_args * enriched_term
  | ET_Test of enriched_term * enriched_term * enriched_term
  | ET_Let of enriched_pattern * enriched_term * enriched_term * enriched_term
	(* The constructs above are considered "simple", not the ones below *)
  | ET_Event of enriched_term * new_args * enriched_term
  | ET_LetFilter of binder list * predicate * enriched_term list * enriched_term * enriched_term
  | ET_Insert of enriched_term * enriched_term
  | ET_Get of enriched_pattern * enriched_term * enriched_term * enriched_term * bool

and enriched_pattern =
    { ep_desc : enriched_pat_desc;
      ep_simple : bool;
      ep_simple_no_restr : bool;
      ep_type : typet }

and enriched_pat_desc =
  | EP_PatVar of binder
  | EP_PatTuple of funsymb * enriched_pattern list
  | EP_PatEqual of enriched_term

(* Environment elements; environments are needed for terms in queries
   that cannot be expanded before process translation, see link PGTLink
   below *)

and envElement =
    EFun of funsymb
  | EVar of binder
  | EName of funsymb
  | EPred of predicate
  | EEvent of funsymb
  | EType of typet
  | ETable of funsymb
  | ELetEq of term * typet
  | ELetFun of (enriched_term list -> enriched_term) * (typet list) * typet
  | EProcess of binder list * process * (int * (string * Parsing_helper.extent)) list
  | EReserved

(* Each restriction "new" is annotated with
   - optionally, the identifiers given between brackets after the "new",
   which serve to determine the arguments in the internal representation
   of the name
   - the current environment at the restriction, which serves to determine
   which variables to use in queries of the form "new a[x = ...]"

Events may also be annotated with identifiers between brackets.
They serve to determine the variables to include in the environment
used for proving injective correspondences.
*)

and new_args = binder list option * envElement StringMap.t

(* Processes *)

and process =
    Nil
  | Par of process * process
  | Repl of process * occurrence
  | Restr of funsymb * new_args * process * occurrence
  | Test of term * process * process * occurrence
  | Input of term * pattern * process * occurrence
  | Output of term * term * process * occurrence
  | Let of pattern * term * process * process * occurrence
  | LetFilter of binder list * fact * process * process * occurrence
  | Event of term  * new_args * process * occurrence
  | Insert of term * process * occurrence
  | Get of pattern * term * process * process * occurrence
  | Phase of int * process * occurrence
  | Barrier of int * (string * Parsing_helper.extent) * process * occurrence
  | AnnBarrier of int * string * funsymb * funsymb * (binder * term) list * process * occurrence
  | NamedProcess of string * term list * process

(* Type of a nounif declaration option *)

type nounif_single_op =
  | Hypothesis
  | Conclusion (* Corresponds to the option [conclusion] *)
  | Ignore (* Corresponds to the option [ignoreAFewTimes] *)

type nounif_op = nounif_single_op list

type nounif_value =
  | NoUnifNegDefault
  | NoUnifPosDefault
  | NoUnifValue of int

(* Rule descriptions for History.get_rule_hist *)

type rulespec =
  | RApplyFunc of funsymb * predicate
  | RApplyProj of funsymb * int * predicate  (* For projections corresponding to data constructors *)
  | RFail of bool * predicate
  | RConclFail of predicate

(* History of construction of rules *)

type onestatus =
    No | NoOcc | WithOcc

type hypspec =
    ReplTag of occurrence * int(*Number of elements of name_params after it*)
  | InputTag of occurrence
  | PreciseTag of occurrence
  | EventTag of occurrence
  | BeginFact
  | LetFilterTag of occurrence (* Destructors succeed *)
  | LetFilterTagElse of occurrence
  | OutputTag of occurrence
  | TestTag of occurrence
  | LetTag of occurrence
  | TestUnifTag of occurrence
  | TestUnifTag2 of occurrence
  | InputPTag of occurrence
  | OutputPTag of occurrence
  | InsertTag of occurrence
  | GetTag of occurrence
  | GetTagElse of occurrence

type label =
    ProcessRule of hypspec list * term list
  | Apply of funsymb * predicate
  | TestApply of funsymb * predicate
  | TestEq of predicate
  | LblEquiv
  | LblClause
  | LblEq
  | Rl of predicate * predicate
  | Rs of predicate * predicate
  | Ri of predicate * predicate
  | Ro of predicate * predicate
  | Rfail of predicate
  | TestComm of predicate * predicate
  | WeakSecr
  | Rn of predicate
  | Init
  | PhaseChange
  | TblPhaseChange
  | LblComp
  | LblNone
  | TestUnif
  | TestDeterministic of funsymb
  | TestTotal of funsymb
  | Goal
  | GoalCombined
  | GoalInjective
  | GenerationNested

(* Ordering *)

(* Ordering in a clause always correspond to the IO-satisfaction relation:
  In  F@i && H -> C@j, we know that if the clause is used then
    - T, i |-_{IO} F
    - T, j |-_{IO} C
  Moreover, is the order is Less (resp. Leq) then i < j (resp. i <= j).

  Nore that we slightly modify the relation |-_{IO} from the technical rapport
  from [BCC22] related to tables. We consider that T, i |-_{IO} table(tbl(M_1,..,M_n))
  holds when T[i] \xrightarrow{\tau} T[i+1] corresponds to the insert rule specifically
  of tbl(M_1,..,M_n). Basically, the satisfaction specifically indicate when the element
  was inserted.
*)

type clause_order =
  | Less
  | Leq

(* Assume a clause F@i && H -> C_1@k_1 && ... && C_n@k_n.  *)
type clause_ordering_relation =
  | CONone
      (* No ordering of F is given (e.g. i can be occur after the conclusion) *)
  | COMax of clause_order
      (* i < max(k_1,...,k_n) when clause_order = Less. Otherwise i <= max(k_1,...,k_n)
        Only used with n > 1. Otherwise we use COSpecific.   
      *)
  | COSpecific of (int * clause_order) list
      (* In [COSpecific ord_l], [ord_l] must be of the form [ (j_1,op_1), ..., (j_r,op_r) ]
         with:
          - 1 <= j_1 < ... < j_r <= n
          - It indicates that for all r, i op_r C_{j_r}   
      *)

(* Ordering in a query may correspond to several semantics. In a correspondence query, 
  F_1@i_1 && .. && F_n@i_n ==> \psi[G@k], the semantics of the premise corresponds to the 
  IO-satisfaction relation but the satisfaction relation of G@k may vary. In particular,
  it can use
    - Standard relation |-_{i}
    - Phaseless relation |-_{p} where attacker and table facts cannot rely on rules I-Phase
      to prove their satisfaction (it can still rely on I-App and I-New)
    - IO relation |-_{IO}
  Note that |-_{IO} \subseteq |-_{p} \subseteq |-_{i}

  See [ordering.mli] for more details.
*)

type satisfaction_semantics =
  | SemIO
  | SemPhaseLess
  | SemStd

type query_order = satisfaction_semantics * clause_order

type query_ordering_relation =
  | QONone
  | QOMax of query_order
  | QOSpecific of (int * query_order) list 

(* Rules *)

type injectivity =
  | DoubleIndex of int * int
  | SingleIndex of fact (* Conclusion fact*) * fact (* Fact to match *) * int
  | NoIndex of fact (* Conclusion facts*)

type t_lemma_kind =
  | Axiom 
  | Lemma
  | Restriction

type t_remove_events_for_lemma =
  | RENone
  | REKeep
  | RERemove

type lemma =
  {
    l_index : int;
    l_premise : fact list;
    l_nb_std_fact : int;
    l_nb_user_fact : int;
    l_subterms : (term * term) list;
    l_constra : constraints;
    l_conclusion : ((fact * query_ordering_relation) list * constraints * (term * term) list) list;
    l_verif_app : bool;
    l_sat_app : bool;
    l_induction : int option;
    l_origin_kind : t_lemma_kind; 
    l_remove_events : t_remove_events_for_lemma
  }

type history =
    Rule of int * label * fact list * fact * constraints
  | Removed of int (* Position of the fact removed *) * int (* Position of the duplicated fact *) * history
  | Any of int (* Position of the fact removed in elim_any_x *) * history
  | Empty of fact (* The history for the intial query goal *)
  | HRemovedBySimplification of int (** Position of the fact removed *) * history
  | HEquation of int * fact * fact * history
  | Resolution of history * int * history
  | TestUnifTrue of int * history
  | HLemma of
      lemma (** Lemma number *) *
      int list (** match of lemma's premises with hypothesis of the clause *) *
      (int list) list (** match of subterm fact in lemma's premises *) *
      (int * bool list) (* Conclusion of lemma [i,is_added]. [i] represents [i]-th disjunct. [is_added] indicates if the each fact in the conclusion of the lemma was added. *) *
      history (* History of the rule on which the lemma is applied *)
  | HCaseDistinction of
      fact (* The conclusion of the clause *) *
      fact list (* The hypotheses *) *
      (term * term) list (* Substitution to apply *) *
      constraints (* Added constraints *) *
      history (* History of the rule on which the verification is applied *)
  | HInjectivity of injectivity * history
  | HNested of
      int list (* Index matching the premise of the nested query *) *
      int (* Nb of fact in the original clause's conclusion *) *
      history
  | HLiveness of int * bool (** Was a fresh occurrence created *)* history 
    

type reduction = fact list * fact * history * constraints

type ordered_reduction =
  {
    rule : reduction;
    order_data : (clause_ordering_relation * int) list;
      (* The integer indicates whether an hypothesis can be
        selected if they matched a nounif declaration with option [ignoreAFewTimes] *)
  }

(* Equational theory *)

type equation = term * term

(* Proof history *)

type addition_label =
  | LAppliedLemmma of lemma
  | LLiveness
  | LCaseDistinction

type added_derivation = addition_label * constraints * fact_tree list

and fact_tree_desc =
    FHAny
  | FEmpty
  | FRemovedBySimplification
  | FRemovedWithProof of fact_tree
  | FRule of int * label * constraints * fact_tree list * added_derivation list
  | FEquation of fact_tree

and fact_tree =
    { mutable desc: fact_tree_desc;
      mutable thefact: fact
    }

(* type of input to the Horn clause resolution solver *)

type t_solver_kind =
    Solve_Standard
  | Solve_CorrespBipro
  | Solve_Equivalence
  | Solve_WeakSecret of (typet * history) list * int
        (* Weaksecr.attrulenum, max_used_phase *)
  | Solve_Noninterf of (funsymb * term list option) list

type clauses =
  | Given of reduction list
  | ToGenerate of reduction list * ((reduction -> unit) -> unit)

type t_horn_state =
    { h_clauses : clauses;
      h_equations : ((term * term) list * eq_info) list;
      h_close_with_equations : bool;
      h_not : fact list;
      h_elimtrue : (int * fact) list;
      h_memberOptim : (predicate * (history * history * funsymb)) list;
      h_equiv : (fact list * fact * int) list;
      h_nounif : (fact_format * nounif_value * nounif_op) list;
      h_clauses_to_initialize_selfun : reduction list;
      h_solver_kind : t_solver_kind;
      h_lemmas : lemma list;
      h_pred_prove : predicate list; (* Predicates that we are trying to prove,
         which must therefore not be removed by eliminating redundant clauses *)
      h_event_in_queries : funsymb list; (*
         Events that occurs in the conclusion of the queries.
         Thus they cannot be removed even when they cannot be used for applying
         a lemma. *)

      (* Second derivations *)
      h_predicates_for_second_saturation : predicate list;
      h_events_for_second_saturation : funsymb list;

      h_ordered_saturation : bool
        (** Indicates whether an ordered saturation is requested. 
            When h_predicate_for_second_saturation <> [] then h_ordered_saturation is necessarily true. *)
    }

(* For precise options *)

type precise_info =
  | Action of typet

(* For translation of terms containing rewrite rules *)

(* The status of a rewrite rule provides some informations on which arguments
   of a rewrite rules should be obtained before obtaning the result of the
   application of the rewrite rule.

   Formally, the status of a rewrite rule g(t_1,...,t_n) -> r, is ToCheck(k_c,k_e) where
    - k_c represents the smallest index such that t_{k_c+1},...,t_n are distinct
      unfailing variables not appearing in t_1,...,t_{k_c}.
      Thus, to check whether the rewrite rule can be applied to some terms u_1,..., u_n,
      we only need to check the matching between t_i and u_i up to index k_c.
    - k_e is the max of k_c and the biggest index i where t_i = r when r is an unfailing variable;
      otherwise k_e = k_c.
      Thus, to obtain the result of the application of the rewrite rule to some terms u_1,..., u_n,
      we only need to compute the matching between t_i and u_i up to index k_e.

      Note that we have as invariant k_c <= k_e.

    The status ToExecute(n) is used during the translation of rewrite rules when we already
    translated the arguments passed the index "k_c".
*)
type rewrite_rules_status =
  | ToCheck of int * int
  | ToExecute of int
