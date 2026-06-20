
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

    module Options =
    struct
      let nopp = ref false
      let noneg = ref false

      let level = ref 0
      let trace = ref false
      let timeout = ref 0
      let verbose = ref false

      let outdir = ref "trace"
      let outtype = ref ""

      let cache = ref true
    end

    let usage name = Printf.sprintf "usage: %s [-options] [file]" name

    let arg_options =
        [
         ("--nopp",  Arg.Set    Options.nopp,  "disable preproc function");
         ("--noneg", Arg.Set    Options.noneg, "disable negation function");

         ("--level", Arg.Int    (fun l -> Options.level := l ), "trace level");
         ("--trace", Arg.Set    Options.trace, "print proof trace");
         ("--time",  Arg.Int    (fun l -> Options.timeout := l), "set exec timeout");
         ("--verbose", Arg.Set    Options.verbose, "print additional information");

         ("--outdir",Arg.String (fun l -> Options.outdir := l),  "set output directory");
         ("--out",   Arg.String (fun l -> Options.outtype := l),  "set output type");

         ("--nocache", Arg.Clear  Options.cache, "disable function memoization");
        ]
    
    let input_file = ref None
    let file f =
        try
            match f with
            |s when Str.string_match (Str.regexp "^[\n\t ]*$") s 0 -> ()
            |_ -> input_file := Some(f)
        with _ -> ()

    let init () = 
        let custom_options =
            try (Option.get (!Logic.__options))
            with Option.No_value -> []
        in
        let _ =
            try Arg.parse (arg_options@custom_options) file (usage Sys.argv.(0))
            with Arg.Bad s -> failwith s
        in 
        OutputBroker.level := !Options.level;
        OutputBroker.trace := !Options.trace
    
    let main
        ?(histlist=[]) ?(varlist=[])
        ?(pp=fun x -> x) ?(neg=fun x -> x)
        ~inputparser ~exitfun ~strategy ~mapcont =
        let ppfun = if !Options.nopp then (fun x -> x) else pp in
        let negfun = if !Options.noneg then (fun x -> x) else neg in
        let newnode s =
            let container = new Container.container mapcont in
            let inputlist =
                Array.of_list (
                    List.map (fun i -> ppfun (negfun i)) (inputparser s)
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
        let file_ch =
            match !input_file with
            |Some(f) -> open_in f
            |None -> stdin
        in
        let read_lines =
            let read_new_line n =
                try Some (input_line file_ch)
                with End_of_file -> None
            in
                Stream.from read_new_line
        in
        (* we stop on a new line, we ignore comments *)
        let rec get_line () =
            match Stream.next read_lines with
            |s when Str.string_match (Str.regexp "^[\n\t ]*$") s 0 -> 
                    raise End_of_file
            |s when Str.string_match (Str.regexp "^#.*$") s 0 -> get_line ()
            |s -> s
        in
        try
            while true do
                try
                    let line = get_line () in
                    let node = newnode line in
                    let _ = 
                        if !Options.verbose
                        then begin 
                            Printf.printf "Proving: %s \n" line;
                            let (cont,_,_) = node#get in
                            Printf.printf "Start Node: %s \n"
                            (UserRule.DataType.Store.to_string cont)
                        end
                        else ()
                    in
                    let cache = (new Cache.cache !Options.cache) in
                    let _ = OutputBroker.rulecounter := 0 in
                
                    let start = Timer.start_timing () in
                    let _ = Timer.trigger_alarm (!Options.timeout) in
                    let result = 
                        let lr = Visit.visit cache strategy node in
                        Llist.hd lr
                    in
                    let time = Timer.stop_timing start in

                    Printf.printf "%s\nResult:%s\nTotal Rules applications:%d\n"
                        (Timer.to_string time)
                        (exitfun result)
                        !OutputBroker.rulecounter;

                    if !Options.cache && !Options.verbose then
                        Printf.printf "%s\n\n"
                        cache#stats
                    else print_newline ();

                    Gc.major ();
                    flush_all ()
                with Timer.Timeout -> Printf.printf "Timeout elapsed\n\n"
            done
        with
        |End_of_file |Stream.Failure -> exit 0
end
