open Parsing_helper
open Types
open Terms
open Clause

let never_select_weight = -10000
let match_concl_weight = -7000
let default_add_no_unif_weight = -5000
let default_user_no_unif_weight = -6000
let default_user_select_weight = 3000
let dummy_weight = -4000

(* The two following lists are sorted by increasing weight *)

let no_unif_set = ref ([] : (fact_format * int) list)
let no_unif_concl_set = ref ([] : (fact_format * int) list)
let no_unif_ignore = ref ([] : fact_format list)


let no_unif_warnings = ref ([] : fact_format list)

let inst_constraints = ref false
let modify_nounif = ref true
let apply_induction = ref true

let weight_of_user_weight = function
  | NoUnifNegDefault -> default_user_no_unif_weight
  | NoUnifPosDefault -> default_user_select_weight
  | NoUnifValue n ->
      if n <= never_select_weight
      then never_select_weight + 1
      else n

(* Add a nounif in the sorted list *)

let rec add_no_unif format weight = function
  | [] -> [format,weight]
  | ((_,w) as fw)::q when w < weight -> fw :: (add_no_unif format weight q)
  | l -> (format,weight)::l

(* Make the variables of a nounif declaration homogeneous, i.e. if a var v is
   tagged with FVar then the function replaces all instances of FAny v by FVar v. *)

let rec mark_format_term id_thread = function
  | FFunApp(_,args) -> List.iter (mark_format_term id_thread) args
  | FVar v ->
      begin match v.link.(id_thread) with
        | FLink (FVar _) -> ()
        | NoLink -> link v (FLink (FVar v))
        | _ -> Parsing_helper.internal_error __POS__ "[selfun.mark_format_term] Unexpected link"
      end
  | FAny v -> ()

let rec follow_link_format_term id_thread = 
  let is_FLink lst = match lst.(id_thread) with FLink _ -> true | _ -> false in
  let is_NoLink lst = match lst.(id_thread) with NoLink -> true | _ -> false in
  function
  | FFunApp(f,args) -> FFunApp(f,List.map (follow_link_format_term id_thread) args)
  | FVar { link = lst; _ } when is_FLink lst -> let FLink t = lst.(id_thread) in t
  | FAny { link = lst; _ } when is_FLink lst -> let FLink t = lst.(id_thread) in t
  | FAny { link = lst } as t when is_NoLink lst -> t
  | _ -> Parsing_helper.internal_error __POS__ "[selfun.follow_link_format_term] Unexpected link"

let homogeneous_format_term_list id_thread tlist =
  Terms.auto_cleanup (fun () ->
    List.iter (mark_format_term id_thread) tlist;
    List.map (follow_link_format_term id_thread) tlist
  )

let homogeneous_format ?(id_thread=0) (p,args) = (p,homogeneous_format_term_list id_thread args)

let initialize ?(id_thread=0) v_no_unif_set solver_kind =

  no_unif_set := [];
  no_unif_concl_set := [];
  no_unif_ignore := [];
  no_unif_warnings := [];

  List.iter (fun (f,nv,opt) ->
    let n = weight_of_user_weight nv in
    let f' = homogeneous_format ~id_thread f in
    List.iter (function
      | Hypothesis -> no_unif_set := add_no_unif f' n !no_unif_set
      | Conclusion -> no_unif_concl_set := add_no_unif f' n !no_unif_concl_set
      | Ignore -> no_unif_ignore := f' :: !no_unif_ignore
    ) opt;

    if !Param.nounif_ignore_once = Param.NIO_All && n < 0 && not (List.exists (fun op -> op = Ignore) opt)
    then no_unif_ignore := f' :: !no_unif_ignore
  ) v_no_unif_set;

  match solver_kind with
    Solve_Equivalence
  | Solve_CorrespBipro
  | Solve_WeakSecret _ ->
     inst_constraints := true
  | _ ->
     inst_constraints := false

let rec has_same_format_term id_thread t1 t2 =
   match (t1,t2) with
   | (FunApp(f1,l1), FFunApp(f2,l2)) ->
        (f1 == f2) && (List.for_all2 (has_same_format_term id_thread) l1 l2)
   | (Var _, FVar v2) | (_, FAny v2) ->
       begin
         match v2.link.(id_thread) with
           NoLink ->
             begin
               if v2.unfailing then
                 begin
                   Terms.link ~id_thread v2 (TLink t1);
                   true
                 end
               else
                 (* v2 is a message variable; the matching works only if t1 is a message *)
                 match t1 with
                   Var v' when v'.unfailing -> false
                 | FunApp(f,[]) when f.f_cat = Failure -> false
                 | _ -> Terms.link ~id_thread v2 (TLink t1); true
             end
         | TLink t1' -> Terms.equal_terms t1 t1'
         | _ -> Parsing_helper.internal_error __POS__ "unexpected link in has_same_format_term"
       end
   | (_,_) -> false

let has_same_format id_thread (c1, p1) (c2, p2) =
  (c1 == c2) && (auto_cleanup (fun () -> List.for_all2 (has_same_format_term id_thread) p1 p2))

let rec find_same_format id_thread f = function
    [] -> 0
  | ((a,n)::l) -> if has_same_format id_thread f a then n else find_same_format id_thread f l

(* Function dealing with induction nounif *)

(* [exists_ignored_nounif ()] returns [true] if and only if some nounif have been
   declared with the option [ignoreAFewTimes]. *)
let exists_ignored_nounif () = !no_unif_ignore != []

let rec implies_format id_thread t1 t2 = match t1,t2 with
  | FFunApp(f1,args1), FFunApp(f2,args2) ->
      f1 == f2 && List.for_all2 (implies_format id_thread) args1 args2
  | FFunApp _, _ -> false
  | FVar v1, FVar _
  | FAny v1, _ ->
      begin match v1.link.(id_thread) with
        | FLink t1' -> Terms.equal_formats t1' t2
        | NoLink -> Terms.link ~id_thread v1 (FLink t2); true
        | _ -> Parsing_helper.internal_error __POS__ "[selfun.implies_format_term] Unexpected link"
      end
  | _ -> false

(* [implies_fact_format f1 f2] returns true when the format [f1] implies format [f2].
   To work properly, [f2] should be homogeneous. *)
let implies_fact_format id_thread (p1,args1) (p2,args2) =
  if p1 == p2
  then
    Terms.auto_cleanup (fun () ->
      List.for_all2 (implies_format id_thread) args1 args2
    )
  else false


let rec compute_match_format t1 t2 =
   match (t1,t2) with
   | (Var v1), (Var _) -> FAny v1
   | (Var v1), _ -> FVar v1
   | (FunApp (f1,l1')), (FunApp (f2,l2')) ->
       if f1 != f2 then internal_error __POS__ "terms do not match 3";
       FFunApp(f1,List.map2 compute_match_format l1' l2')
   | _,_ -> internal_error __POS__ "terms do not match 4"

let compute_match_format_fact f1 f2 = match (f1,f2) with
  Pred(c1, p1), Pred(c2, p2) ->
    if c1 != c2 then
      internal_error __POS__ "facts do not match";
    (c1, List.map2 compute_match_format p1 p2)

let rec already_implied_format_by_lower_weight id_thread format = function
  | [] -> false
  | (f,n)::q when n <= default_add_no_unif_weight ->
      if implies_fact_format id_thread f format
      then true
      else already_implied_format_by_lower_weight id_thread format q
  | _ -> false



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

  (** [selection_fun_ignore_nounif cl] checks whether one hypothese of [cl] can be 
      matched with a nounif declared with option [ignoreAFewTimes]. When it is the case,
      the function returns the position of the hypothesis selected as well as the update
      clause. When no hypothesis is authorized, the function returns -1 and the outputted
      clause is physicall the same as [cl]. *)
  val selection_fun_ignore_nounif : ?id_thread:int -> clause -> int * clause
end

module Make
  (H:HypSig)
  (C:ClauseSig with type hyp = H.hyp) 
  (Q:Database.QueueSig with type clause = C.clause)
  (W:Weaksecr.WeakSecrSig with type clause = C.clause)
  (N:Noninterf.NonInterfSig with type clause = C.clause) : 
  SelfunSig with type clause = C.clause and type queue = Q.t
=
struct 
  type clause = C.clause
  type queue = Q.t

  open C

  (** [term_warning cl] displays a termination warning when the clause unifies with itself. 
      Only applies to old selection functions. *)
  let term_warning cl =
    Display.stop_dynamic_display ();
    if !Param.max_depth < 0 
    then
      begin
        if !Param.should_stop_term || !Param.verbose_term 
        then
          begin
            print_string "Termination warning: The following clause unifies with itself\n";
            C.Text.display_indep cl;
            print_string "The saturation process will probably not terminate\n"
          end;
        if !Param.should_stop_term 
        then
          begin
            print_string "You have several solutions to guarantee termination:\n";
            print_string " - limit the depth of terms with param maxDepth = <depth>.\n";
            print_string " - add one of the unifying facts of this clause to the set\n";
            print_string "   of facts on which unification is forbidden, with nounif <fact>.\n";
            print_string " - add a clause that is more general than all clauses generated by the\n";
            print_string "   unifications of the above clause. (Maybe you have already done that, and I\n";
            print_string "   did not detect it. If so, ignore this message by pressing [return].)\n";
            print_string "Press [return] to continue, [ctrl-c] to stop\n";
            Param.should_stop_term := false;
            ignore(read_line())
          end
      end

  (** The selection functions *)

  let selection_fun_nounifset id_thread cl =
    let rec sel (nold, wold) n = function
      | [] ->
          if !modify_nounif  && nold >= 0 && Terms.matchafactstrict cl.conclusion (H.get_fact (List.nth cl.hypotheses nold))
          then  term_warning cl;
          nold
      | h::l when is_unselectable (H.get_fact h) ->
            (* Guarantee that p(x) is never selected when we decompose data
               constructors on p, except that we can select the conclusion when
               all hypotheses and the conclusion are of the form p(x) for
               such p. This is important for the soundness of
               the decomposition of data constructors. *)
          sel (nold, wold) (n+1) l
      | h::l -> 
          let Pred(p,lp) as f = H.get_fact h in
          let wnew = find_same_format id_thread (p,lp) (!no_unif_set) in
          if wnew <> 0 then
            if wnew > wold
            then sel (n,wnew) (n+1) l
            else sel (nold, wold) (n+1) l
          else
            begin
              if (matchafactstrict cl.conclusion f) && (!modify_nounif) then term_warning cl;
              n
            end
    in
    if is_unselectable cl.conclusion then
      (* The conclusion is never selected if an hypothesis can be *)
      sel (-1, never_select_weight) 0 cl.hypotheses
    else
      (* The conclusion can be selected if we don't find better in
         the hypothesis *)
      let Pred(p,args) = cl.conclusion in
      let w = find_same_format id_thread (p,args) !no_unif_concl_set in
      if w <> 0
      then sel (-1, w) 0 cl.hypotheses
      else sel (-1, -1) 0 cl.hypotheses

  (* Very good for skeme, but slightly slower for some other protocols *)

  let selection_fun_nounifset_maxsize id_thread cl =
    let rec sel (nold, wold) n = function
        [] ->
          if !modify_nounif && nold >= 0 && matchafactstrict cl.conclusion (H.get_fact (List.nth cl.hypotheses nold))
          then term_warning cl;
          nold
      | f::l when is_unselectable (H.get_fact f) ->
            (* Guarantee that p(x) is never selected when we decompose data
              constructors on p, except that we can select the conclusion when
              all hypotheses and the conclusion are of the form p(x) for
              such p. This is important for the soundness of
              the decomposition of data constructors. *)
          sel (nold, wold) (n+1) l
      | h::l ->
          let Pred(p,lp) as f = H.get_fact h in
          let wtmp = find_same_format id_thread (p,lp) (!no_unif_set) in
          let wnew =
            if wtmp <> 0
            then wtmp
            else fact_size f
          in
          if wnew > wold
          then sel (n,wnew) (n+1) l
          else sel (nold, wold) (n+1) l
    in
    if is_unselectable cl.conclusion then
      (* The conclusion is never selected if an hypothesis can be *)
      sel (-1, never_select_weight) 0 cl.hypotheses
    else
      (* The conclusion can be selected if we don't find better in
        the hypothesis *)
      match cl.conclusion with
        | Pred(p,args) ->
            let w = find_same_format id_thread (p,args) !no_unif_concl_set in
            if w <> 0
            then sel (-1, w) 0 cl.hypotheses
            else sel (-1, -1) 0 cl.hypotheses

  
  (* Very good for termination - even if it does not solve all cases, of course *)

  let selection_fun_weight id_thread cl =
    (* [(nold, wold)] is the information for the hypotheses that are not more general than the conclusion.
     [(nold_m,wold_m,hold_m)] is the information for the hypotheses that are more general than the conclusion.
     We prefer selecting a hypothesis that is not more general than the conclusion, to avoid cycles, 
     hence [nold] when it is not -1.
    *)
    let rec sel (nold, wold) (nold_m,wold_m,hold_m) n = function
      | [] ->
          (* If [nold = -1] and [nold_m = -1] then the conclusion is selected 
           and there is no other matching fact available. We check if a fact
          from the hypotheses strictly matches the conclusion.
           
           If [nold = -1] and [nold_m <> -1] then we can select the fact that matches the 
           conclusion (i.e. [nold_m]) but we display a warning that it may lead to non 
           termination.

           If [nold <> -1] then we select [nold] without displaying any termination warnings.
          *)
          if nold = -1 && nold_m = -1 && !modify_nounif then (* conclusion selected *)
            begin
              List.iter (function h ->
                if matchafactstrict cl.conclusion (H.get_fact h) then
                  begin
                    let format = compute_match_format_fact (H.get_fact h) cl.conclusion in
                    let format' = homogeneous_format ~id_thread format in

                    (* We add a nounif if it is not already implied by a nounif with smaller weight *)
                    if not (already_implied_format_by_lower_weight id_thread format' !no_unif_set) then
                      begin
                        no_unif_set := add_no_unif format' default_add_no_unif_weight !no_unif_set;
                        if !Param.nounif_ignore_once <> Param.NIO_None
                        then no_unif_ignore := format' :: !no_unif_ignore;
                        if !Param.verbose_term then
                          begin
                            Display.stop_dynamic_display ();
                            print_string "select ";
                            Display.Text.display_fact_format format';
                            print_string ("/" ^ (string_of_int default_add_no_unif_weight));
                            Display.Text.newline()
                          end
                      end
                  end) cl.hypotheses
            end;

          if nold = -1 && nold_m <> -1 && wold_m >= 0 && !modify_nounif
          then 
            begin
              let format = compute_match_format_fact hold_m cl.conclusion in
              let format' = homogeneous_format ~id_thread format in
  
              if not (List.exists (fun f -> implies_fact_format id_thread f format') !no_unif_warnings)
              then
                begin
                  no_unif_warnings := format' :: !no_unif_warnings;
                  Display.auto_cleanup_display (fun () ->
                    Display.stop_dynamic_display ();
                    print_string "Termination warning: Selecting an hypothesis matching the conclusion.\nIn case of non-termination, try a noselect declaration implying the following one:\n";
                    print_string "   noselect ";
                    let v_list = ref [] in
                    List.iter (get_vars_acc_format v_list) (snd format');
                    if !v_list <> []
                    then 
                      begin 
                        Display.Text.display_list (fun v -> 
                          Display.Text.display_var v;
                          Display.Text.print_string ":";
                          Display.Text.print_string v.btype.tname
                        ) ", " !v_list;
                        Display.Text.print_string "; "
                      end;
                    Display.Text.display_fact_format format';
                    print_string ".\n"
                  )
                end
            end;

          let sel_fact = if nold <> -1 then nold else nold_m in

          if !Param.verbose_term && ((wold < 0 && nold >= 0) || (nold = -1 && wold_m < 0 && nold_m >= 0) (* || (wold < -1) *) ) && !modify_nounif then
            begin
              Display.stop_dynamic_display ();
              print_string "Termination warning: ";
              C.Text.display_indep cl;
              print_string ("Selecting " ^ (string_of_int sel_fact));
              Display.Text.newline()
            end;
  
          sel_fact
      | (f::l) when is_unselectable (H.get_fact f) ->
            (* Guarantee that p(x) is never selected when we decompose data
              constructors on p. This is important for the soundness of
              the decomposition of data constructors. *)
          sel (nold, wold) (nold_m,wold_m,hold_m) (n+1) l
      | h::l ->
          let Pred(p,lp) as f = H.get_fact h in
          let wnew =
            let wtmp_0 = find_same_format id_thread (p,lp) (!no_unif_set) in
            let wtmp_1 =
              if wtmp_0 > match_concl_weight && matchafactstrict cl.conclusion f
              then match_concl_weight
              else wtmp_0
            in
            if wtmp_1 <> 0 then wtmp_1 else
            if !Param.select_fun == Param.TermMaxsize then fact_size f else 0
          in

          if wnew <= wold && wnew <= wold_m
            then sel (nold, wold) (nold_m, wold_m, hold_m) (n+1) l
            else
              if Terms.are_matched_facts (H.get_fact h) cl.conclusion
              then 
                if wnew > wold_m 
                then sel (nold, wold) (n, wnew, H.get_fact h) (n+1) l
                else sel (nold, wold) (nold_m, wold_m,hold_m) (n+1) l
              else
                if wnew > wold
                then sel (n, wnew) (nold_m, wold_m, hold_m) (n+1) l
                else sel (nold, wold) (nold_m, wold_m, hold_m) (n+1) l
    in
    let wconcl =
      if is_unselectable cl.conclusion then
        (* The conclusion is never selected if an hypothesis can be *)
        never_select_weight
      else
        match cl.conclusion with
          Pred(p, []) when p == Param.dummy_pred -> dummy_weight
        | Pred(p,args) ->
            (* The conclusion can be selected if we don't find better in
              the hypothesis *)
            let wtmp_0 = find_same_format id_thread (p,args) !no_unif_concl_set in
            let wtmp_1 =
              if wtmp_0 > match_concl_weight && List.exists (fun h -> matchafactstrict (H.get_fact h) cl.conclusion) cl.hypotheses
              then match_concl_weight
              else wtmp_0
            in
            if wtmp_1 <> 0 then wtmp_1 else -1
    in
    sel (-1, wconcl) (-1,wconcl,cl.conclusion) 0 cl.hypotheses

  (* Avoid creating cycles when instantiating in inst_constra:
  renames all variables to unused ones. *)
  let rec false_copy = function
    Var v -> Terms.new_var_def_term v.btype
  | FunApp(f,l) -> FunApp(f, List.map false_copy l)

  let inst_constra id_thread = function
  | (Var v,t) ->
      if v.link.(id_thread) = NoLink then
        Terms.link ~id_thread v (TLink (false_copy t))
  | _ -> ()

  let selection_fun ?(id_thread=0) cl =
    let r = match !Param.select_fun with
      | Param.NounifsetMaxsize -> selection_fun_nounifset_maxsize id_thread cl
      | Param.Term | Param.TermMaxsize -> selection_fun_weight id_thread cl
      | Param.Nounifset -> selection_fun_nounifset id_thread cl
    in
    let r =
      (* For proofs of equivalences (!inst_constraints = true),
        if the conclusion is selected (r = -1) and it is unselectable,
        that is, it is of the form such as bad: or attacker:x,x',
        then we try to find a better selection by selecting an hypothesis
        attacker:x,x' in which x (or x') occurs in an inequality x <> M. *)
      if (r = -1) && (!inst_constraints) && (is_unselectable cl.conclusion) then
        begin
          let cl2 = 
            Terms.auto_cleanup_noexception (fun () -> 
              List.iter (List.iter (inst_constra id_thread)) cl.constraints.neq;
              C.copy2 cl
            )
          in
          
          match !Param.select_fun with
          | Param.NounifsetMaxsize -> selection_fun_nounifset_maxsize id_thread cl2
          | Param.Term | Param.TermMaxsize -> selection_fun_weight id_thread cl2
          | Param.Nounifset -> selection_fun_nounifset id_thread cl2
        end
      else r
    in
    let r =
      if r = -1 then N.selfun cl else r
    in
    if r = -1 then W.selfun cl else r
  
  let initialize_before_saturation ?(id_thread=0) rulequeue =
    (* If no "nounif" instruction is given, first guess them by "selection_fun_weight" *)
    if !no_unif_set = [] || !Param.select_fun == Param.Term || !Param.select_fun == Param.TermMaxsize
    then
      Q.iter (fun (r,_,_) -> ignore (selection_fun_weight id_thread r)) rulequeue

  let hypothesis_is_in_conclusion hyp concl = 
    let concl_list = fact_list_of_conclusion concl in
    List.exists (Terms.equal_facts hyp) concl_list

  (** [selection_fun_ignore_nounif cl] checks whether one hypothesis of [cl] can be 
      matched with a nounif declared with option [ignoreAFewTimes]. When it is the case,
      the function returns the position of the hypothesis selected as well as the updated
      clause. When no hypothesis is authorized, the function returns -1 and the outputted
      clause is physically the same as [cl]. *)
  let selection_fun_ignore_nounif ?(id_thread=0) cl =

    let rec explore_hyp n prev_hypl = function
      | []-> None (* No need hypothesis selected *)
      | hyp :: q_hypl ->
          let Pred(p,args) = H.get_fact hyp in
          if H.can_ignore_nounif hyp && List.exists (has_same_format id_thread (p,args)) !no_unif_ignore
          then 
            (* A format has been matched *)
            let hyp' = H.decrease_ignore_nounif_authorization hyp in
            Some (n,{ cl with hypotheses = List.rev_append prev_hypl (hyp'::q_hypl) })
          else if !Param.nounif_ignore_conclusion && not (is_unselectable (H.get_fact hyp)) && hypothesis_is_in_conclusion (H.get_fact hyp) cl.conclusion 
          then Some (n,cl)
          else
            (* No format has been matched *)
            explore_hyp (n+1) (hyp::prev_hypl) q_hypl
    in

    match explore_hyp 0 [] cl.hypotheses with
      | Some(n,cl') -> n,cl'
      | None -> -1,cl  

  (** Similar to [selection_fun] except that the automatic detection of nounif has been deactivated. *)
  let selection_fun_nostatechange ?(id_thread=0) rule =
    modify_nounif := false;
    let r = selection_fun ~id_thread rule in
    modify_nounif := true;
    r
end


module Std = Make(Hyp)(Std)(Database.QueueClause)(Weaksecr.Std)(Noninterf.Std)
module Ord = Make(HypOrd)(Ord)(Database.QueueOrdClause)(Weaksecr.Ord)(Noninterf.Ord)
