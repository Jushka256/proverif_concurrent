
type token
type flag

val create_flag : unit -> flag
val create_token : ?lim:int -> flag -> token
val set_token : token -> unit
val check_token : token -> (token -> bool) -> bool

(** explain *)
val list_exists : flag -> (token -> 'a -> bool) -> 'a list -> bool 
val bool_function_list_or : flag -> (token -> bool) list ->  bool
val or_function : flag -> (token -> bool) -> (token -> bool) -> bool
(* Add comments! *)