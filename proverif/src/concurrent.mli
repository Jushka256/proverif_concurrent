
type token
type flag

(** Creates a flag, which is the shared boolean interrupt that concurrent functions use to terminate each other *)
val create_flag : unit -> flag

(** Creates a token given a flag, which is a counter unique to one function that checks the shared flag occasionally *)
val create_token : ?lim:int -> flag -> token

(** Takes a token, sets the flag portion of the token to be true *)
val set_token : token -> unit

(** Takes a token and continuation function, returns true if the flag is set otherwise runs the continuation.  For use with Or *)
val check_token : token -> (unit -> 'a) -> (unit -> 'a) -> 'a

(** Runs a boolean function on each element of a list concurrently, returns or of results *)
val list_exists : flag -> (int -> token -> 'a -> bool) -> 'a list -> bool 

(** Runs a list of boolean functions concurrently, returns or of results *)
val bool_function_list_or : flag -> (int -> token -> bool) list ->  bool

(** Returns or of running two functions concurrently *)
val or_function : flag -> (int -> token -> bool) -> (int -> token -> bool) -> bool

val run_concurrent : (unit -> 'a) -> 'a