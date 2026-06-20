
module Make(MapCont : sig type t class set : [t] TwbSet.ct end)
           (SblCont : sig type t class set : [t] TwbSet.ct end)
           (H : TwbSet.ValType) (V : TwbSet.ValType) = struct

    type history_type = History | Variable

    module Substitution = TwbSbl.Make(SblCont)
    module Container = TwbContainer.Make(
        struct
            type t = MapCont.t
            type map = (MapCont.t, MapCont.set) TwbContainer.ct
        end)
    module Hmap = TwbHash.Make(H)
    module Vmap = TwbHash.Make(V)

    module Store =
        struct
            type store = Container.container
            let copy s = s#copy
            let to_string s = s#to_string
            let make () = failwith "ever used ?"
        end

    module History =
        struct
            type store = Hmap.map
            let copy s = s#copy
            let to_string s = s#to_string
            let make () = new Hmap.map
        end

    module Variable =
        struct
            type store = Vmap.map
            let copy s = s#copy
            let to_string s = s#to_string
            let make () = new Vmap.map
        end

    module NodeType =
        struct
            type elt = ( Store.store * History.store * Variable.store )
            let copy (m,h,v) = ( Store.copy m, History.copy h, Variable.copy v )
            let to_string (m,h,v) =
                Printf.sprintf "%s\n%s\n%s"
                (Store.to_string m)
                (History.to_string h)
                (Variable.to_string v)
            let marshal (m,h,_) =
                string_of_int 
                (Hashtbl.hash ((Store.to_string m)^(History.to_string h)))
        end

    module Node = Node.Make(NodeType)
    module Cache = Cache.Make(Node)
        
    module NodePatternFunc = NodePattern

    module NodePattern = NodePatternFunc.Make(
        struct
            type t = MapCont.t
            type hist = History.store
            type var = Variable.store
            type sbl = Substitution.sbl
            type container = Store.store
        end
    )

    module Partition = Partition.Make(NodePattern)
    module Build = Build.Make(NodePattern)

    module RuleContext = RuleContext.Make(Node)(NodePattern)
    module Rule =
        struct
        type t = RuleContext.t
        type node = Node.node
        type tree = node Tree.tree
        type result = node Tree.result
        type context_type = RuleContext.ct
        type context = RuleContext.context
        class virtual rule =
            object
                method virtual check : node -> context
                method virtual down  : context -> tree
                method virtual up    : context -> result Llist.llist -> result
                method virtual use_cache : bool
            end
    end

    module Visit = Visit.Make(Node)(Rule)

end
