(* Extended list mosdule *)

module List : 
sig
  include module type of struct include List end

  (** [crop n l] returns the list composed of the first n elements of [l]. *)
  val crop : int -> 'a list -> 'a list

  (** [split_nth n l] returns the lists [(l1,l2)] where [l = l1 @ l2] and [length l1 = n]. 
    @exit when [n > length l]. *)
  val split_nth : int -> 'a list -> 'a list * 'a list

  (** [remove_i p l] returns [None] if for all elements [x] of [l], [p x = false]. 
    Otherwise, if [x] is the first element of [l] such that [p x = true] then 
    [remove_i p l] returns [Some(i,x,l')] where [i] is the position of [x] in [l]
    and [l'] is the list [l] with [x] removed. *)
  val remove_i : ('a -> bool) -> 'a list -> (int * 'a * 'a list) option

  (** [mapq f l] applies [f] to every elements of [l]. It preserves physical equalities
    if the application of [f] on elements of [l] also preserves physical equality. Formally,
      if [l = [x1;...;xn]] and [f xi == xi],...,[f xn == xn] 
      then the sublist [[f xi;...;f xn]] is physically equal to [[xi;...;xn]]. *)
  val mapq : ('a -> 'a) -> 'a list -> 'a list

  (** [find_map f l] returns [None] if [f] returns [None] for all elements
      of [l], [Some x] for the first element of [l] such that [f] returns
      [Some x] otherwise *)
  val find_map : ('a -> 'b option) -> 'a list -> 'b option
      
  (** [filter_map f l] applies [f] to every element of [l], filters out the 
      None elements and returns the list of the arguments of the Some elements. 
    *)
  val filter_map : ('a -> 'b option) -> 'a list -> 'b list

  (** [filter_map2 f l1 l2] applies [f] to every element of [l1] and [l2], filters out the 
      None elements and returns the list of the arguments of the Some elements. 
      @exit if the sizes of [l1] and [l2] are different. *)
  val filter_map2 : ('a -> 'b -> 'c option) -> 'a list -> 'b list -> 'c list

  (** [replace_assq f a l] replace the first pair [(a,b)] of [l] by [(a,f a b)] if any. *)
  val replace_assq : ('a -> 'b -> 'b) -> 'a -> ('a * 'b) list -> ('a * 'b) list  

  (** [create f n] creates the list [[f 1;...;f n]]. *)
  val create : (int -> 'a) -> int -> 'a list

  (** [find_and_replace f1 f2 l] finds the first element [x] in [l] satisfying [f1 x]
      and replaces it with [f2 x]. When such element exists, the function returns 
      [Some (i,l')] with [l'] being the updated list, [i] the position of [x] in [l];
      and otherwise it returns [None]. *)
  val find_and_replace : ('a -> bool) -> ('a -> 'a) -> 'a list -> (int * 'a list) option
end
