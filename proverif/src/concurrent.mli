
type token

val create_flag : unit -> token
val create_token : unit -> token
val set_token : token -> unit
val check_token : token -> (token -> bool) -> bool

(** explain *)
val list_exists : (token -> 'a -> bool) -> 'a list -> (*int ->*) bool 
val bool_function_list_or : (token -> bool) list -> (*int ->*) bool

(* Add comments! *)