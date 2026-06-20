
module Make(MapCont : sig type t class set : [t] TwbSet.ct end)
           (SblCont : sig type t class set : [t] TwbSet.ct end)
           (H : TwbSet.ValType) (V : TwbSet.ValType) = struct

    module UserRule = UserRule.Make(MapCont)(SblCont)(H)(V)
    open UserRule.DataType
    
    module Logic = 
    struct
        let __substitute : (MapCont.t -> MapCont.t -> MapCont.t -> MapCont.t) option ref = ref None
        let __simplification : (MapCont.t -> MapCont.t -> MapCont.t ) option ref = ref None
        let __options : (Arg.key * Arg.spec * Arg.doc) list option ref = ref None
        let __use_cache : bool ref = ref false
    end 

    let init () =
        OutputBroker.level := 0;
        OutputBroker.trace := false

    let main_aux
        ?(histlist=[]) ?(varlist=[])
        ?(pp=fun x -> x) ?(neg=fun x -> x)
        ~inputparser ~exitfun ~strategy ~mapcont line =
        let newnode s =
            let container = new Container.container mapcont in
            let inputlist =
                Array.of_list (
                    List.map (fun i -> pp (neg i)) (inputparser s)
                )
            in
            let cont =
                Array.fold_left(fun cont (i,il) ->
                    (cont)#set i ((cont#get i)#addlist "" il)
                ) container (Array.mapi(fun i il -> (i,il)) inputlist)
            in
            let hmap =
                List.fold_left (fun acc (s,v) -> acc#add s v) 
                (new Hmap.map) histlist
            in
            let vmap =
                List.fold_left (fun acc (s,v) -> acc#add s v) 
                (new Vmap.map) varlist
            in
            new Node.node (cont,hmap,vmap)
        in
        try
            let node = newnode line in
            let cache = (new Cache.cache true) in
            let _ = OutputBroker.rulecounter := 0 in
            let start = Timer.start_timing () in
            let _ = Timer.trigger_alarm 60 in
            let result = 
                let lr = Visit.visit cache strategy node in
                Llist.hd lr
            in
            let time = Timer.stop_timing start in
            Printf.sprintf "%s\nResult:%s\nTotal Rules applications:%d\n"
                (Timer.to_string time)
                (exitfun result)
                !OutputBroker.rulecounter

        with Timer.Timeout -> Printf.sprintf "Timeout elapsed\n\n"

let main ?(histlist=[]) ?(varlist=[])
        ?(pp=fun x -> x) ?(neg=fun x -> x)
        ~inputparser ~exitfun ~strategy ~mapcont =

        let input =
            main_aux ~histlist:histlist ~varlist:varlist
            ~pp:pp ~neg:neg ~inputparser:inputparser
            ~exitfun:exitfun ~strategy:strategy ~mapcont:mapcont in

        let server =
            (* for testing purposes a cgi can be run as a server *) 
            if false then new XmlRpcServer.netplex ()
            else new XmlRpcServer.cgi ()
        in
        server#register "prover"
        ~help:"Run the TWB prover"
        ~signatures:[[`String; `String]]
        (function
            |[`String s] -> `String (input s)
            |_ -> XmlRpcServer.invalid_params ()
        );
        server#run () 

end
