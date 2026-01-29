
type flag = bool Atomic.t 
type token = int ref * int * flag

let limit : int = 100

let create_flag : flag = Atomic.make false

let create_token ?(lim=limit) (fl:flag) = (ref 0, lim, fl)

let set_token (tkn : token) =
  let (count_ref, lim, fl) = tkn in
  Atomic.set fl true

(** [check_token] is designed to or, as it returns true when stopped *)
let check_token (tkn : token) (f : token -> bool) = 
  let (count_ref, lim, fl) = tkn in
  incr count_ref;
  (!count_ref mod lim = 0 && Atomic.get fl) || f tkn

module T = Domainslib.Task
let numCores = 4 (*Domainslib.Domains.num_domains ()*)
let pool = T.setup_pool ~num_domains:numCores ()

let bool_function_list_or (fns : (token -> bool) list) fl : bool =
  let promises = List.map (fun fn -> T.async pool (fun () -> fn (create_token fl))) fns in
  List.exists (fun p -> T.await pool p) promises

let list_exists (f: token -> 'a -> bool) (l : 'a list) flag =
  let promises = List.map (fun a -> T.async pool (fun () -> f (create_token flag) a)) l in
  List.exists (fun p -> T.await pool p) promises


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
