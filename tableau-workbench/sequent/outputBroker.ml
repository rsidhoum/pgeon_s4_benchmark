(*
module Broker =
    struct

    let readCond = Condition.create ()
    let msgQueue = Queue.create ()
    let mutex = Mutex.create ()

    let add str =
        Mutex.lock mutex ;
        Queue.add str msgQueue ;
        Condition.signal readCond ;
        Mutex.unlock mutex

    let wait () =
        Mutex.lock mutex ;
        while Queue.length msgQueue = 0 do
            Condition.wait readCond mutex
        done

    let process () =
        let str = Queue.take msgQueue in
        print_string str ;
        flush stdout ;
        Mutex.unlock mutex

    let printer () =
        while true do
            wait ();
            process ();
        done
    end
*)
let trace = ref false
let level = ref 0
let rulecounter = ref 0

let print_down_aux name sbl node parentid =
    let _ = incr rulecounter in
    if !trace then
        begin
            if !level > 0 then
                Printf.printf "Substitution List: \n%s\n----\n" sbl#to_string
            else ()
            ;
            let (m,h,_) = node#get in
            let s = if !level > 0 then "Apply: " else "" in
            Printf.printf
            "%s%s ( %d -> %d )\n%s\n%s\n"
            s name parentid !rulecounter m#to_string (h#to_string)
        end
    else ()

let print_up_aux name node =
    if !trace && !level > 0 then
        begin
            let (_,_,v) = node#get in
            Printf.printf
            "Up %s \n%s\n----\n"
            name (v#to_string)
        end
    else ()

let print_check_aux name node =
    if !trace && !level > 1 then
        begin
            let (m,h,_) = node#get in
            Printf.printf
            "Check %s \n%s\n%s\n-----\n"
            name m#to_string (h#to_string)
        end
    else ()

    (*
let print_down name sbl node parentid = Broken.add 0 (print_down_aux name sbl node parentid)
let print_up name node = Broker.add 0 (print_up_aux name node)
let print_check name node = Broker.add 0 (print_check_aux name node)
*)
let print_down name sbl node parentid = print_down_aux name sbl node parentid
let print_up name node = print_up_aux name node
let print_check name node = print_check_aux name node
