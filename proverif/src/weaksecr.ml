open Types
open Terms
open Clause

let weaksecret_mode = ref false
let attrulenum = ref []
let max_used_phase = ref 0

let initialize = function
    Solve_WeakSecret(v_attrulenum, v_max_used_phase) ->
     weaksecret_mode := true;
     attrulenum := v_attrulenum;
     max_used_phase := v_max_used_phase
  | Solve_Equivalence | Solve_CorrespBipro ->
     weaksecret_mode := true;
     attrulenum := [];
     max_used_phase := 0
  | _ ->
     weaksecret_mode := false;
     attrulenum := [];
     max_used_phase := 0

(* When [t1 = f(...)] for a data constructor [f], unify [t2] with
   [f(x1...xn)], and symmetrically. 
   When t2 <> f(x1...xn) forall x1...xn we can derive bad by the clause
     att'(f(x1...xn),x) && x <> f(g1...gn) -> bad
   obtained from a projection clause
     att'(f(x1...xn),x) && x <> f(g1...gn) -> att'(xi, fail)
   by [Rules.simplify_conclusion].
   This is sound even in the presence of equational theories: 
   if [t2] unifies with  [f(x1...xn)] modulo the equational theory,
   then there is a clause for which it unifies syntactically. *)
let rec match_data_symbol t1 t2 = match t1 with
  | Var v1 ->
      begin match Terms.get_link v1 with
      | TLink t1' -> match_data_symbol t1' t2
      | _ ->
          match t2 with 
          | Var v2 -> 
              begin match Terms.get_link v2 with
              | TLink t2' -> match_data_symbol t1 t2'
              | _ -> ()
              end
          | FunApp({ f_cat = Tuple; _ } as f,_) ->
              (* By the first 2 cases, v has no link *)
              (* Printf.printf "FOUND ONE !!!\n";
              Display.Text.display_rule_indep r;
              flush_all (); *)
              let vars = Terms.var_gen (fst f.f_type) in
              Terms.link v1 (TLink (FunApp(f,vars))) 
          | _ -> ()
      end
  | FunApp(f1,_) ->
      match t2 with 
      | Var v2 -> 
          begin match Terms.get_link v2 with 
          | TLink t2' -> match_data_symbol t1 t2'
          | _ -> 
              if f1.f_cat = Tuple
              then 
                (* By the first 2 cases, v has no link *)
                (* Printf.printf "FOUND ONE !!!\n";
                Display.Text.display_rule_indep r;
                flush_all (); *)
                let vars = Terms.var_gen (fst f1.f_type) in
                Terms.link v2 (TLink (FunApp(f1,vars))) 
              else ()
          end
      | FunApp(f2,_) ->
          if (f1.f_cat = Tuple || f2.f_cat = Tuple) && f1 != f2 then raise Unify

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

module Make 
  (H:HypSig)
  (C:ClauseSig with type hyp = H.hyp) =
struct
  open C 

  type clause = C.clause

  (* Standard clauses *)
  let detect_atteq = function
    | { hypotheses = [h1;h2];
        conclusion = Pred(p4, []);
        constraints = { neq = [[(Var v5, Var v6)]]; is_nat = []; is_not_nat = []; geq = [] };
        _
      } ->
        begin match H.get_fact h1, H.get_fact h2 with
          | Pred(p1, [Var v1; Var v2]), Pred(p2, [Var v3; Var v4]) when 
            p1.p_prop land Param.pred_ELIMVAR != 0
            && p2.p_prop land Param.pred_ELIMVAR != 0
            && p4 == Param.bad_pred
            && (
              (v1 == v3
              && ((v2 == v5 && v4 == v6) || (v2 == v6 && v4 == v5)))
              ||
              (v2 == v4
              && ((v1 == v5 && v3 == v6) || (v1 == v6 && v3 == v5)))
            ) -> true
          | _ -> false
        end
    | _ -> false

  let detect_atteq2 = function
    | { hypotheses = [h1;h2];
        conclusion = Pred(p4, []);
        constraints = { neq = [[(Var v5, Var v6)]]; is_nat = []; is_not_nat = []; geq = [] };
        _
      } ->
        begin match H.get_fact h1, H.get_fact h2 with
          | Pred(p1, [Var v1]), Pred(p2, [Var v3; Var v4]) when
            p1.p_prop land Param.pred_ATTACKER != 0
            && p2.p_prop land Param.pred_ELIMVAR != 0
            && p4 == Param.bad_pred
            && (v1 == v3 || v1 == v4)
            && ((v3 == v5 && v4 == v6) || (v3 == v6 && v4 == v5)) -> true
          | _ -> false
        end
    | _ -> false

  let is_standard_clause cl =
    (detect_atteq cl) || (detect_atteq2 cl) ||
    (match cl.history with
    | Rule (_,Apply(f,_),_,_,_)
    | Resolution(Rule(_,Apply(f,_),_,_,_),0,Rule(-1,Rfail _,_,_,_)) ->
        Terms.is_proj f
        (* Clause att'(f'(x1...xn),x) && x <> f'(g1...gn) -> bad
           and the symmetric one
           where f is a projection for data constructor f', 
           obtained from a projection clause
             att'(f'(x1...xn),x) && x <> f'(g1...gn) -> att'(xi, fail)
           by [Rules.simplify_conclusion], which generates the history 
           as if a resolution with the Rfail clause
             att'(x, fail) -> bad 
           had happened. Note that, in most cases, the resolution between
           the projection clause and Rfail will not happen because
           the hypothesis is generally selected in the projection clause, 
           so it is important that [Rules.simplify_conclusion] generates 
           the clause
             att'(f'(x1...xn),x) && x <> f'(g1...gn) -> bad.
           The projection clause 
             att'(f'(x1...xn),x) && x <> f'(g1...gn) -> att'(xi, fail)
           must not be subject to other transformations, in particular
           not [match_data_symbol] and not application of lemmas.
           *)
    | _ -> false)

  (* Simplification rules *)

  let elim_att_guess_xx next_stage repeat_next_stage cl =
    let redo_all_optim = ref false in
    let hist' = ref cl.history in
    let rec f n = function
      | [] -> []
      | hyp :: l ->
          match H.get_fact hyp with 
            | Pred({ p_info = AttackerGuess _}, [Var v1; Var v2]) when v1 == v2 ->
              redo_all_optim := true;
              hist' := Resolution(List.assq (Param.get_type v1.btype) (!attrulenum), n, !hist');
              (* We use C.generate_hyp_strictly_before for the added hypotheses.
                 It's ok since in the trace, the attacker guess is done at the end of the trace.
              *)
              H.create_strictly_before (Pred(Param.get_pred (Attacker(!max_used_phase, v1.btype)), [Var v1])) hyp :: (f (n+1) l)
            | _ -> hyp :: (f (n+1) l)
    in
    let hypl = f 0 cl.hypotheses in
    if !redo_all_optim then
      repeat_next_stage { cl with hypotheses = hypl; history = !hist' }
    else
      next_stage cl

  (** [remove_equiv_events] removes H in clauses H -> bad when H just contains events
      and we are dealing with a proof of equivalence. In this case, events just serve
      for triggering lemmas, we do not need them in such a clause.
      
      @since 2.05 "The history is updated."
  *)
  let remove_equiv_events next_stage cl =
    if !weaksecret_mode && Terms.is_bad cl.conclusion && 
      List.for_all (function hyp -> 
        let Pred(p,_) = H.get_fact hyp in
        Param.event2_pred_block == p
      ) cl.hypotheses
    then 
      let hist' = List.fold_left (fun acc _ -> HRemovedBySimplification(0,acc)) cl.history cl.hypotheses in
      next_stage { cl with hypotheses = []; history = hist' }
    else next_stage cl

  (** Calls to [simplify] are prevented on standard clauses (clauses such that
      [is_standard_clause] returns true) in rules.ml *)
  let simplify next_stage repeat_next_stage cl =
    if not (!weaksecret_mode)
    then
      next_stage cl
    else
      let rec find_att x = function
        | [] -> false
        | hyp :: l ->
            match H.get_fact hyp with
              | Pred(p', [t]) when p'.p_prop land Param.pred_ATTACKER != 0 && Terms.equal_terms t x -> true
              | _ -> find_att x l
      in
      let rec find_right x y = function
        | [] -> None
        | hyp :: l ->
            match H.get_fact hyp with
              | Pred(p', [t1; t2]) when p'.p_prop land Param.pred_ELIMVAR != 0 && Terms.equal_terms t1 x && not (Terms.equal_terms t2 y) -> Some t2
              | _ -> find_right x y l
      in
      let rec find_left x y = function
        | [] -> None
        | hyp :: l ->
            match H.get_fact hyp with 
              | Pred(p', [t1; t2]) when p'.p_prop land Param.pred_ELIMVAR != 0 && Terms.equal_terms t2 x && not (Terms.equal_terms t1 y) -> Some t1
              | _ -> find_left x y l
      in

      let nat_vars = TermsEq.gather_nat_vars cl.constraints in
      let rec is_public = function
        | Var v ->
            if Param.get_ignore_types () then
              List.memq v nat_vars
            else
              Terms.equal_types v.btype Param.nat_type
        | FunApp(f,args) ->
            (not f.f_private) && (not (f.f_cat = Failure)) && (List.for_all is_public args)
      in

      let rec inst = function
        | [] -> ()
        | (h::qr) ->
            begin
            match H.get_fact h with
            (* A previous version asked t1, t2, t1', t2' to be variables; we now do it with terms. *)
            | Pred(p, [t1; t2]) when (Terms.unblock_predicate p).p_prop land Param.pred_ELIMVAR != 0 ->
                begin
                  (* pred_ELIMVAR means AttackerBin or AttackerGuess
                    attacker'(M,M) is true for all public terms M (combinations of natural numbers and public functions).
                    So if attacker'(M,M') is true and M is a public term,
                    then either M <> M' and we derive bad by attacker'(x,y) && attacker'(x,y') && y <> y' -> bad
                    or M = M' => we can unify M and M'. *)
                  if is_public t1 || is_public t2 then
                    Terms.unify t1 t2
                  else
                  (* If attacker'(M,M') and attacker'(M,M'') are in the hypothesis of the
                    clause, either M' <> M'' and we derive bad by attacker'(x,y) && attacker'(x,y') && y <> y' -> bad
                    or M' = M'' => we can unify M' and M''.
                    attacker(M) is the same as attacker(M,M).
                    The clause attacker'(x,y) && attacker'(x,y') && y <> y' -> bad must be kept for this to be sound,
                    this is guaranteed by [is_standard_clause]. *)
                  if find_att t1 cl.hypotheses || find_att t2 cl.hypotheses then
                    Terms.unify t1 t2
                  else
                    match find_right t1 t2 qr with
                      Some t2' -> Terms.unify t2' t2
                    | None ->
                        match find_left t2 t1 qr with
                          Some t1' -> Terms.unify t1' t1
                        | None ->
                            match_data_symbol t1 t2
                end
            | _ -> ()
            end;
            inst qr
      in
      
      let r = 
        try
          auto_cleanup (fun () ->
            inst cl.hypotheses;
            if !Terms.current_bound_vars.(Terms.default_thread_id) != []
            then Some(true,C.copy2 cl)
            else Some(false,cl)
          )
        with Unify -> None
      in
      match r with
        | Some(true,cl) -> repeat_next_stage cl
        | Some(false,cl) -> elim_att_guess_xx next_stage repeat_next_stage cl
        | None -> () 
        

  (* Selection function: called when the standard selection function says
    to select the conclusion *)

  let selfun cl =
    if not ((!weaksecret_mode) && (Terms.is_bad cl.conclusion) && (cl.hypotheses != []) && List.exists (function hyp -> let Pred(p,_) = H.get_fact hyp in Param.event2_pred_block != p) cl.hypotheses) then -1
    else
    if (detect_atteq cl)then 0 else
    begin
      print_string "Termination warning: selection not found in Weaksecr.selfun in rule\n";
      C.Text.display_indep cl;
      -1
    end
end


module Std = Make(Hyp)(Std)
module Ord = Make(HypOrd)(Ord)
