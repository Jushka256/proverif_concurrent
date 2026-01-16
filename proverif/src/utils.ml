(* Extended list module *)

module List = 
struct
  include(List)

  let[@tail_mod_cons] rec crop n = function
    | [] -> []
    | x::l -> if n = 0 then [] else x::(crop (n-1) l)

  let rec split_nth n = function
    | q when n = 0 -> [], q
    | t::q ->
        let (l1,l2) = split_nth (n-1) q in
        (t::l1,l2)
    | [] -> Parsing_helper.internal_error __POS__ "[Utils.List.split] Wrong parameter."

  let rec remove_i_aux i p = function
    | [] -> None
    | x::q ->
        if p x 
        then Some(i,x,q)
        else 
          match remove_i_aux (i+1) p q with
            | None -> None
            | Some(i',x',q') -> Some(i',x',x::q')

  let remove_i p l = remove_i_aux 0 p l

  let rec mapq f l = match l with
    | [] -> l
    | t::q ->
        let t' = f t in
        let q' = mapq f q in
        if (t == t') && (q == q') then l else t'::q'

  let rec find_map f = function
    | [] -> None
    | a::l ->
	match f a with
	| (Some x) as r -> r
	| None -> find_map f l
						    
  let[@tail_mod_cons] rec filter_map f = function
    | [] -> []
    | x :: q ->
        match f x with
        | None -> filter_map f q
        | Some v -> v :: filter_map f q

  let[@tail_mod_cons] rec filter_map2 f l1 l2 = match l1, l2 with
    | [], [] -> []
    | x1 :: q1, x2 :: q2 ->
        begin match f x1 x2 with
        | None -> filter_map2 f q1 q2
        | Some v -> v :: filter_map2 f q1 q2
        end
    | _ -> Parsing_helper.internal_error __POS__ "[Utils.List.filter_map2] Both list should have the same size."

  let[@tail_mod_cons] rec replace_assq f a = function
    | [] -> []
    | (key,x)::q ->
        if key == a 
        then (key,f key x)::q 
        else (key,x)::(replace_assq f a q)

  let rec create_aux acc f = function
    | 0 -> acc
    | n -> create_aux ((f n)::acc) f (n-1)

  let create f n = create_aux [] f n

  let rec find_and_replace_aux i f_test f_repl = function
    | [] -> None
    | x::q when f_test x ->
        Some(i,(f_repl x::q))
    | x::q ->
        match find_and_replace_aux (i+1) f_test f_repl q with
        | None -> None
        | Some(idx,l) -> Some(idx,x::l)

  let find_and_replace f_test f_repl l =
    find_and_replace_aux 0 f_test f_repl l
end
