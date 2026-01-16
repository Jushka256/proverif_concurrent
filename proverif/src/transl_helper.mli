open Types
open Clause
open Parsing_helper

(** Clause generation helper *)

(** Removal of all may-fail terms:
  
  A may fail term may only occur at top level in three predicates:
    - att(u)
    - attBin(u,v)
    - attGuess(u,v)
  Note that attGuess and attBin behave typically the same way. 
  Constraints never contain may-fail variables. (They have been removed
  from constraints of destructor rules by [Terms.generate_destructor_with_side_cond].)

  When working on non-interference properties, the may-fail variables may also appear in testunif predicates.
  In such a test, the may-fail terms appear only in clauses for destructor function symbols:
    testunif((v1,...,vn),EVar(N1,...,Nn)) && att(v1) && ... && att(vn) ==> bad
  In that clause, all v1,...,vn are may-fail variables. So when simplifying the clauses, 
    if Ni is not a may-fail term then vi will be instantiated by Ni.
    if Ni is fail then vi will be instantiated by Ni
    if Ni is a may-fail variable then it will only be unified with vi. Another Nj may be equal 
      to Ni  
  Hence, we can: 
    - Replace each vi with fail if Ni is a may-fail term and otherwise replace vi with a classical variable.
      (The case of several Ni that are the same may-fail variable and vi is a classical variable is subsumed
      by the clause att(x) && att(y) && testunif(x,y) -> bad.) 
    - In the testunif predicate, we remove the fail component.

  We consider the following 4 rules:
  1- If H -> att(u) then we can instantiate u with a classic variable x as instantiating u with fail
    would be subsumed by the clause -> att(fail)
     If H -> attBin(fail,u), then can instantiate u with a classic variable x as instantiating u with fail
    would be subsumed by the clause -> attBin(fail,fail). We have the symmetrical case + the two cases with attGuess.
  2- If R = attBin(fail,v) && H -> C and R is not the clause Rfail = (attBin(fail,x) -> bad) then v = fail.
    Indeed, if v <> fail then it would be subsumed by Rfail. We have the symmetrical case + the two cases with attGuess.
     If R = attBin(fail,M) && H -> C where M is not fail nor a may-fail variable
     and R is not the clause Rfail = (attBin(fail,x) -> bad) then 
     remove the clause (it is subsumed by Rfail).
  3- If R = attBin(M,v) && H -> C where M is not fail nor a may-fail variable and 
    R is not the clause Rfail = (attBin(x,fail) -> bad) then v = y with y a fresh variable
    Indeed, if v = fail then it would be subsumed by Rfail. We have the symmetrical case + the two cases with attGuess.
  4- If H -> attBin(u,v) then we can instantiate in three possibilities (x,y), (x,fail), (fail,y)
     If H -> attBin(M,v) then we can instantiate v in two possibilities y or fail.
     We have the symmetrical case + the cases with attGuess.

  Procedure: 
    0) In case of non-interference, simplify testunif as outlined above.
    1) Apply the first three rules as long as we can.
    2) Remove tautologies
    3) If C contains may-fail variables, apply rule 4 and restart (when the result is (M,fail) or (fail,M), replace by bad)
    4) If C does not contain may-fail variables then remove all facts containing may-fail variables.
       (because the remaining hypotheses that contain may-fail variables can only be
       att(u), attBin(u,v), attGuess(u,v) and these facts are satisfiable)

  The instantiation of variables and removal of hypotheses are done separately.
*)

(** [instantiate_may_fail f_next hypl concl constra tags] instantiates all may-fail variables in clause with
    hypotheses [hypl], conclusion [concl], constraints [constra] and tags [tags]. The function may modify the facts testunif
    in [hypl]. The new instantiated version of [hypl], [concl], [constra] and [tags] is given to [f_next]. *)
val instantiate_may_fail : (fact list -> fact -> constraints -> label -> unit) -> fact list -> fact -> constraints -> label -> unit

(** [clauseOrd_of_reduction f_next r] takes a reduction obtained after translation and transforms it into an ordered clause. *)
val clauseOrd_of_reduction : (Ord.clause -> unit) -> reduction -> unit

(** [clause_of_reduction f_next r] takes a reduction obtained after translation and transforms it into a clause. *)
val clause_of_reduction : (Std.clause -> unit) -> reduction -> unit

(** [remove_subsumed_attacker_clauses_before_display r_ref n_ref] reorganize [!r_ref] by removing subsumed reductions. 
    New rule numbers are given. *)
val remove_subsumed_attacker_clauses_before_display : reduction list ref -> int ref -> unit

(** [set_membership_predicates p_decl_l] returns the list of membership predicates with the rule history
    of the init and recursive membership clauses. *)
val set_membership_predicates : reduction list -> (predicate * funsymb option) list -> (predicate * (history * history * funsymb)) list

(** [check_membership ext memberOptim hypl constra concl] checks if [hyp && constra -> concl] forms
    a clause corresponding to membership of a predicate declared in [memberOptim]. *)
val check_membership : extent -> (predicate * funsymb option) list ref -> fact list -> constraints -> fact -> unit
(** [forbid_equiv_membership ext memberOptim hypl concl] displays an error message when the
    equivalence clause [hypl <=> concl] uses a predicate declared in [memberOptim]. *)
val forbid_equiv_membership : extent -> (predicate * funsymb option) list ref -> fact list -> fact -> unit
