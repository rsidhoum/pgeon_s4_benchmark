
open Llist
open Node
open Tree

class type ['a] ct = 
    object('c)
        method get : 'a
        method set : 'a -> 'c
        method is_valid : bool
    end
    
module type S =
    sig
        type t
        type node
        type context_type
        type context = context_type ct
        type tree = node Tree.tree
        type result = node Tree.result

        class virtual rule :
            object
                method virtual check : node -> context
                method virtual down  : context -> tree
                method virtual up    : context -> result Llist.llist -> result
                method virtual use_cache : bool
            end
      end
