
open Unix
open Str
open Findlib


module Options = struct
    let verbose = ref false
    let debug = ref false
    let output = ref ""
    let bytecode = ref false
    let cgi = ref false
    
    let clean = ref false
    
    let tmp = ref ""
end

let options = [
    ("-v",  Arg.Set Options.verbose, "verbose");
    ("-o",  Arg.Set_string Options.output,  "<file> Set output file name to <file>");

    ("-d", Arg.Set Options.debug, "save the pre-processor output");
    
    ("-t",  Arg.Set_string Options.tmp,  "temporary directory");
    
    ("--cgi", Arg.Set Options.cgi, "Compile the cgi interface");
    ("--clean", Arg.Set Options.clean, "clean the temporary directory")
]

let usage = "usage: compile [-options] <files>" 

let input_filelist = ref []
let file f =
    try
        match f with
        |s when Str.string_match (Str.regexp "^[\n\t ]*$") s 0 -> ()
        |s ->
                let l = Str.split (Str.regexp "[ \t]+") s in
                input_filelist := !input_filelist @ l
    with _ -> () 

let print_verbose fmt_etc =
    let print s = 
        if (!Options.verbose) then (
            Printf.printf "%s" s;
            Pervasives.flush Pervasives.stdout
        )
        else (
            print_string ".";
            Pervasives.flush Pervasives.stdout
        ) 
    in
    Printf.ksprintf print fmt_etc

let run cmd =
    match system cmd with
    |WEXITED 0 -> ()
    |WEXITED code ->
            failwith (Printf.sprintf "command exited with status %d: %s" code cmd)
    |WSIGNALED signal ->
            failwith (Printf.sprintf "command killed by signal %d: %s" signal cmd)
    |WSTOPPED signal ->
            failwith (Printf.sprintf "command stopped by signal %d: %s" signal cmd)

let str_lib_loc =
    try Findlib.package_directory "str"
    with No_such_package (p,i) -> failwith p^i

let ext_lib_loc =
    try Findlib.package_directory "extlib"
    with No_such_package (p,i) -> failwith p^i

let twb_lib_loc =
    try Findlib.package_directory "twb"
    with No_such_package (p,i) -> failwith p^i

let tmp_dir =
    match !Options.tmp with
    |"" ->
            let str = "/tmp/twb" ^ Sys.getenv("LOGNAME") in
            let _ = 
                try ignore(Unix.stat str) with
                |Unix.Unix_error(_) -> 
                        begin Printf.printf "Notice: create directory %s\n" str;
                        ignore(Unix.mkdir str 0o755) end
            in str ^ "/"
    |s -> s ^ "/"

let noext filename =
    if Str.string_match (Str.regexp "^\\(.*\\).ml$") filename 0 then
        Str.matched_group 1 filename
    else
        filename
  
let read_lines fc =
    let read_new_line n = 
        try Some (input_line fc)
        with End_of_file -> None
    in
        Stream.from read_new_line

(* pre-processing *)
let pp filename =
   let debug = if !Options.debug then " --debug " else "" in
   let cgi = if !Options.cgi then " --cgi " else "" in
   print_verbose "Pre-processing: %s\n" filename;
   let cmd = 
       "camlp5o "^
       str_lib_loc ^ "/str.cma "^
       str_lib_loc ^ "/unix.cma "^
       twb_lib_loc ^ "/pa_sequent.cma "^
       "pr_o.cmo "^ 
       filename ^ 
       debug ^
       cgi ^
       " > "^
       tmp_dir ^ filename
   in
   print_verbose "%s\n" cmd;
   run cmd;
   print_verbose "Done.\n"
 
let rec get_line ch () =
    let aux s =
        let ms = Str.replace_first (Str.regexp "\\") "" (Str.matched_group 1 s) in
        let l = Str.split (Str.regexp "[ \t]+") ms in
        List.map (fun s -> 
            ignore(Str.string_match (Str.regexp "\\(.*\\).cmo") s 0);
            (Str.matched_group 1 s)
        ) l
    in
    match Stream.next ch with
    |s when Str.string_match (Str.regexp "^.*.cmo: \\(.*\\)$") s 0 ->
            aux s
    |s when Str.string_match (Str.regexp "^\\(.*.cmo[^:].*\\)$") s 0 ->
            aux s
    |s -> get_line ch ()
 
let rec loop ch l =
    try
        let dl = get_line ch () in
        loop ch (dl@l) 
    with End_of_file |Stream.Failure -> l

let read_native_dependencies filename =
    let fc = open_in filename in
    let buffer = Buffer.create 256 in
    let rec read () =
        try
            Buffer.add_string buffer (input_line fc);
            Buffer.add_char buffer ' ';
            read ()
        with End_of_file -> close_in fc
    in
    read ();
    let output =
        Str.global_replace (Str.regexp "\\\\") " " (Buffer.contents buffer)
    in
    let dependencies =
        try
            let separator = String.index output ':' in
            String.sub output (separator + 1) (String.length output - separator - 1)
        with Not_found -> ""
    in
    List.fold_right (fun dependency acc ->
        if Filename.check_suffix dependency ".cmx" then
            Filename.chop_extension dependency :: acc
        else
            acc
    ) (Str.split (Str.regexp "[ \t\r\n]+") dependencies) []

let rec uniq = function
    |[] -> []
    |h::t -> h:: uniq (List.filter (fun x -> not(x = h)) t)

let rec deps deplist filename =
    let cmd = Printf.sprintf 
       "ocamldep -native %s%s > %s%s.deps.txt"
       tmp_dir filename tmp_dir filename
    in
    pp filename;
    run cmd;
    let l =
        List.filter (fun f -> not(List.mem f deplist))
            (read_native_dependencies (tmp_dir ^ filename ^ ".deps.txt"))
    in
    let ol = List.map (fun f -> deps (f::deplist) (f^".ml") ) l in
    List.append deplist (List.flatten ol)

let remove_files ?(mask=[]) dir =
    let l =
        if mask = [] then "/*.cm* *.o"
        else
            List.fold_left (fun s ss -> s^ss) "/" (
            List.map (fun s -> s^".cm* "^s^".o ") mask
            )
    in
    let cmd = "rm -f "^dir^l in
    print_verbose "Cleaning: %s\n" cmd;
    ignore(system cmd);
    print_verbose "Done.\n"

let compile_quite filename deplist =
    let dl = List.fold_left (fun s ss ->
        Printf.sprintf "%s %s" s ss) "" 
        (List.map (fun s -> s^".ml") deplist)
    in
    let pkgs =
        if !Options.cgi
        then "xmlrpc-light,twb,twb.cgi" 
        else "twb,twb.cli"
    in
    let output =
        if !Options.cgi then (noext(filename)^".cgi") else
        if !Options.output = "" then (noext(filename)^".twb")
        else !Options.output
    in
    let cgi = if !Options.cgi then " -ppopt --cgi " else "" in
    let cmd = Printf.sprintf
    "ocamlfind ocamlopt -syntax twb -package %s %s -linkpkg %s -o %s"
    pkgs dl cgi output
    in
    print_verbose "Compiling: %s\n" cmd;
    run cmd;
    print_verbose "Done.\n"

let main () =
    let _ =
        try Arg.parse options file usage
        with Arg.Bad s -> failwith s
    in
    if !Options.clean then
        begin
            remove_files tmp_dir;
            remove_files (Unix.getcwd ());
            exit(1)
        end
    else
        List.iter( fun filename ->
            let deplist = List.rev(uniq(deps [noext(filename)] filename)) in
            compile_quite filename deplist;
            remove_files ~mask:deplist (Unix.getcwd ());
        ) !input_filelist ;
        print_endline "Done."

let _ = main ()
