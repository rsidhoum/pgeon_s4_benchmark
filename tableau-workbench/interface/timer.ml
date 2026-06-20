
exception Timeout
open Unix

let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout)
let old_behavior = ref (Sys.signal Sys.sigalrm sigalrm_handler)
let update_ob () = old_behavior := Sys.signal Sys.sigalrm sigalrm_handler

let start_timing () =
    let _ = update_ob () in
    Unix.times ()

let stop_timing start =
    let stop = Unix.times () in
    (stop.tms_utime -. start.tms_utime)

let trigger_alarm timeout =
    let _ = Unix.alarm timeout in
    Sys.set_signal Sys.sigalrm !old_behavior

let to_string usertime =
    Printf.sprintf "Time:%.4f" usertime 
