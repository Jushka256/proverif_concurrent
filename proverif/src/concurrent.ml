module Concurrent = 
  struct

    type flag = bool ref
    type token = int ref * int * flag

    val create_flag : unit -> flag = Atomic.make false

    val create_token : int -> flag -> token = 
      fun lim fl-> (ref 0, lim, fl)

    val set_token (tkn : token) : unit =
      let (count_ref, lim, stop_ref) = tkn in
      Atomic.set stop_ref true

    val check_token (tkn : token) (f : token -> bool) : bool =
      let (count_ref, lim, stop_ref) = tkn in
      if !count_ref >= lim then
        if Atomic.get stop_ref then true
        else count_ref := ref 0
      else count_ref := !count_ref + 1
      f tkn


    module T = DomainsLib.Task
    let numCores = DomainsLib.Domains.num_domains ()
    let pool = T.setup_pool ~num_domains:numCores ()

    val list_exists (fns : (token -> bool) list) (lim : int) : bool =
      let fl = create_flag () in
      let promises = List.map (fun fn -> T.async pool (fun () -> fn (create_token lim fl))) fns in
      List.exists List.map (fun p -> T.await pool p) promises


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

  end 