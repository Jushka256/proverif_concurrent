
val set_token : token -> unit
val check_token : token -> (token -> bool) -> bool

val list_exists : (token -> bool) list -> int -> bool

