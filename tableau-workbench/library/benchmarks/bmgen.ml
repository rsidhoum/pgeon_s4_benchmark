
module Opt = struct
    let debug = ref false
    let n = ref 1
    let name = ref ""
    let tmp = ref ""
end

OPTIONS
     ("-d", (Arg.Set Opt.debug), "Enable debug");
     ("-n", (Arg.Int (fun n -> Opt.n := n )), "Number of tests");
     ("-b",  (Arg.Set_string Opt.name),  "select the benchmark to run");
     ("-t",  (Arg.Set_string Opt.tmp),  "temporary directory")
END


let modules = Hashtbl.create 17;;
let are_loading = Hashtbl.create 17;;

let find_in_path path name =
    let filename = ((String.uncapitalize name) ^ ".cmo") in
    if not (Filename.is_implicit filename) then
        if Sys.file_exists filename then filename else raise Not_found
        else
            begin
                let rec try_dir = function
                    | [] -> raise Not_found
                    | dir::rem ->
                            let fullname = Filename.concat dir filename in
                            if Sys.file_exists fullname then fullname
                            else try_dir rem
                in try_dir path
            end
;;

let rec load_module modname path =
    try
        Hashtbl.find modules modname
    with
        Not_found ->
            try
                Hashtbl.add modules modname ();
                Hashtbl.add are_loading modname ();
                (* Printf.printf "Loading: %s ..." modname; *)
                Dynlink.loadfile (modname);
                (* print_endline "done."; *)
                Hashtbl.remove are_loading modname
            with
            | Dynlink.Error(Dynlink.Unavailable_unit(depend))
            | Dynlink.Error(
                Dynlink.Linking_error(_,Dynlink.Undefined_global(depend))
                ) ->
                    begin
                        try
                            if Hashtbl.mem are_loading depend
                            then failwith ("Crossing with "^depend);
                            load_module (find_in_path path depend) path;
                            Hashtbl.remove modules modname;
                            load_module modname path
                        with Not_found ->
                            failwith ("Cannot find "
                            ^String.lowercase(depend)^" in "^
                            (List.fold_left (fun s x -> s^x) " " path))
                    end
            | Dynlink.Error(e) -> failwith (Dynlink.error_message e)
;;

let load pathlist name =
    try
        Dynlink.init();
        Dynlink.default_available_units ();
        load_module (find_in_path pathlist name) pathlist
    with Not_found -> failwith "Loading error"
;;

let tmp_dir =
    match !Opt.tmp with
    |"" ->
            let str = "/tmp/twb" ^ Unix.getlogin () in
            let _ =
                try ignore(Unix.stat str) with
                |Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
            in str ^ "/"
    |s -> s ^ "/"
;;


let sof f = (!Basictype.string_of_formula f) ;;
let print_formula t = Printf.printf "%s\n" (sof t) ;;

let repeat s n =
    for i = 1 to n do
        Printf.printf "#%s not-provable\n" s;
        print_formula (!Common.notprovable i);
        Printf.printf "#%s provable\n" s ;
        print_formula (!Common.provable i);
        flush_all ();
    done
;;

let main () =
    ignore(Twb.init ());
    load [tmp_dir] !Opt.name;
    repeat !Opt.name !Opt.n
;;


main ();;
