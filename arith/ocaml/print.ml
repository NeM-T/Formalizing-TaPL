open Eval

let rec eval_string t =
  match t with
  | Tru -> "Tru"
  | Fls -> "Fls"
  | If (t1, t2, t3) -> "If" ^ (eval_string t1) ^ (eval_string t2) ^ (eval_string t3)
  | O   -> "0"
  | Succ t1 -> "S (" ^ (eval_string t1) ^ ")"
  | Pred t1 -> "Pred" ^ (eval_string t1)
  | Iszero t1 -> "If0" ^ (eval_string t1)


let rec manyeval t1 =
  match eval1 t1 with
  | Some t1' -> manyeval t1'
  | _        -> t1

let get () =
    while true do
      let lexbuf = Lexing.from_channel stdin in
      let result = Parser.toplevel Lexer.main lexbuf in
      print_string (eval_string (manyeval result)); print_newline()
    done


let () =
  match (Array.length Sys.argv) with
    1 -> get ()
  | _ ->
      let file = Sys.argv.(1) in
      let oc   = open_in file in
      let line = try input_line oc with End_of_file -> close_in oc; "End" in
      let lexbuf = Lexing.from_string line in 
      let result = Parser.toplevel Lexer.main lexbuf in
      print_string (eval_string (manyeval result)); print_newline()

