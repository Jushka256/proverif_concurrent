val equal_terms_with_links : ?id_thread:int -> Types.term -> Types.term -> bool
val equal_facts_with_links : ?id_thread:int -> Types.fact -> Types.fact -> bool

val equal_closed_terms : ?id_thread:int -> Types.term -> Types.term -> bool
val equal_closed_facts : ?id_thread:int -> Types.fact -> Types.fact -> bool

val equal_tags : ?id_thread:int -> Types.label -> Types.label -> bool
val equal_constra : ?id_thread:int -> Types.constraints -> Types.constraints -> bool

val match_terms : ?id_thread:int -> Types.term -> Types.term -> unit

val get_vars : ?id_thread:int -> Types.binder list ref -> Types.term -> unit
val has_vars : ?id_thread:int -> Types.term -> bool
