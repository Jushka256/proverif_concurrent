
type flag = bool Atomic.t
type token = int ref * int * flag

let limit : int = 100

let create_flag : flag = Atomic.make false

let create_token : (*int ->*) flag -> token = 
  fun (*lim*) fl-> (ref 0, limit, fl)

let set_token (tkn : token) : unit =
  let (count_ref, lim, fl) = tkn in
  Atomic.set fl true

let check_token (tkn : token) (f : token -> bool) : bool =
  let (count_ref, lim, fl) = tkn in
  let stop = ref false in 
  if !count_ref >= lim then (
      stop := Atomic.get fl;
      count_ref := 0 )
  else (
    count_ref := !count_ref + 1 );
  if !stop then true else f tkn


module T = Domainslib.Task
let numCores = 4 (*Domainslib.Domains.num_domains ()*)
let pool = T.setup_pool ~num_domains:numCores ()

let bool_function_list_or (fns : (token -> bool) list) (*(lim : int)*) : bool =
  let fl = create_flag in
  let promises = List.map (fun fn -> T.async pool (fun () -> fn (create_token (*lim*) fl))) fns in
  List.exists (fun a -> a) (List.map (fun p -> T.await pool p) promises)

let list_exists (f: token -> 'a -> bool) (lst : 'a list) (*(lim : int)*) : bool =
  let fns = List.map (fun a -> fun (tkn : token) -> f tkn a) lst in
  bool_function_list_or fns (*lim*)


(* Need to coordinate checking/setting the flag, I'm thinking atomic actions will make this 
easiest *)

(* We don't want two functions that are running concurrently to be using the same counter even
if they are using the same interrupt flag.  So to do list_exists we want to create one flag
and then one token for each function in the list all using the same flag, potentially with
different limits. *)

(* Is there any actual need for the result structure??  Could just return true if interrupted,
let the computation run if not.  Would be simlist throughout, can add result back in later
if it becomes apparent it is necessary (ie if we did more than just an or) *)

(* As stands the functions need to be correctly augmented with both set_token and check_token
calls in order for this all to work correctly. *)

(* So in terms of the actual functions I'd previously implemented, the first was list_exists 
which did what List.exists does - takes a boolean function and a list and returns the big or 
of that function applied to each element of the list.  Then I also had a separate function which
took a list of functions and simply implemented that concurrently.  I'm thinking that I still define
both of those here, and just use the function one to define the list_exists one*)

(* For simplicity have hard coded the limit specification for now *)
