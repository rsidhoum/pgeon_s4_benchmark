type tptp_status =
  | Theorem
  | Unsatisfiable
  | NonTheorem
  | Satisfiable
  | Unsolved
  | UnknownStatus

let contains sub s =
  try
    let _ = Str.search_forward (Str.regexp_string sub) s 0 in
    true
  with Not_found -> false

let string_to_status s =
  let s = String.lowercase_ascii s in
  if contains "unsatisfiable" s then Unsatisfiable
  else if contains "counter" s && contains "satisfiable" s then NonTheorem
  else if contains "non-theorem" s then NonTheorem
  else if contains "theorem" s then Theorem
  else if contains "satisfiable" s then Satisfiable
  else if contains "unsolved" s then Unsolved
  else UnknownStatus

let extract_status filename =
  let ic = open_in filename in
  let rec parse_lines is_qmltp current_status =
    try
      let line = input_line ic in
      if String.length line > 0 && line.[0] <> '%' then current_status
      else
        let l_low = String.lowercase_ascii line in
        if contains "file" l_low && contains "qmltp" l_low then
          parse_lines true current_status
        else if is_qmltp && contains "s4" l_low then
          if current_status <> UnknownStatus then
            parse_lines is_qmltp current_status
          else
            let clean_line =
              String.map (fun c -> if c = '\t' then ' ' else c) l_low
            in
            let words =
              String.split_on_char ' ' clean_line
              |> List.filter (fun s -> s <> "")
            in
            let status =
              match words with
              | "%" :: "s4" :: _varying :: _cumulative :: constant_status :: _
                ->
                  string_to_status constant_status
              | _ ->
                  let rec find_constant_before_version = function
                    | status_candidate :: version_str :: _
                      when String.length version_str > 0
                           && version_str.[0] = 'v' ->
                        string_to_status status_candidate
                    | _ :: rest -> find_constant_before_version rest
                    | [] -> current_status
                  in
                  find_constant_before_version words
            in
            parse_lines is_qmltp status
        else if (not is_qmltp) && contains "status" l_low then
          let status = string_to_status l_low in
          parse_lines is_qmltp status
        else parse_lines is_qmltp current_status
    with End_of_file -> current_status
  in
  let final_status = parse_lines false UnknownStatus in
  close_in_noerr ic;
  final_status

let to_string = function
  | Theorem -> "Theorem"
  | Unsatisfiable -> "Unsatisfiable"
  | NonTheorem -> "NonTheorem"
  | Satisfiable -> "Satisfiable"
  | Unsolved -> "Unsolved"
  | UnknownStatus -> "UnknownStatus"

let expected_result = function
  | Theorem | Unsatisfiable -> Some "Close"
  | NonTheorem | Satisfiable -> Some "Open"
  | Unsolved | UnknownStatus -> None
