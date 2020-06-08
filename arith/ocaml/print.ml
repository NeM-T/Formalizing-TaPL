open Eval
open Parser


let rec eval_string t =
  match t with
  | Tru -> "Tru"
  | Fls -> "Fls"
  | If (t1, t2, t3) -> "If " ^ (eval_string t1) ^ " THEN " ^ (eval_string t2) ^ " ELSE " ^ (eval_string t3)
  | O   -> "0"
  | Succ t1 -> "S (" ^ (eval_string t1) ^ ")"
  | Pred t1 -> "Pred " ^ (eval_string t1)
  | Iszero t1 -> "If0 " ^ (eval_string t1)


let rec manyeval t1 =
  match eval1 t1 with
  | Some t1' -> manyeval t1'
  | _        -> t1


let write t =
  let parse = Parser.toplevel Lexer.main t in
  let result = manyeval parse in
  let ()     = if (isval result) = False then
    print_string "NotValue : " else
    print_string "Eval : " in
  print_string ((eval_string parse) ^ " -> "); print_string (eval_string result); print_newline()


let rec get () =
  let rec getin () =
  let lexbuf = Lexing.from_channel stdin in
    write lexbuf; get ()
  in
  try getin () 
  with
  | Lexer.Error m -> print_string m; print_newline(); get() 
  |_eRR -> print_string "Parser Error"; print_newline(); get()


let readfile () = 
      let file = Sys.argv.(1) in
      let oc   = open_in file in
      let rec ww () =
        let line = input_line oc in
        let lexbuf = Lexing.from_string line in 
        write lexbuf; ww ()
      in
      try ww ()
      with
        End_of_file     -> close_in oc
      | Lexer.Error mes -> print_string mes; print_newline()
      | eRR             -> print_string "Parser Error"; print_newline()

let () =
  match (Array.length Sys.argv) with
    1 -> get ()
  | _ -> readfile ()

