open Arith

let write t =
  let parse = Parser.toplevel Lexer.main t in
  match Eval.has_type parse with
  | SomeT _ -> 
    let result = Print.manyeval parse in
      if (Eval.value result) = False then
        print_string "実装が悪い" else
          print_string ("Eval : " ^ Print.eval_string parse);
      print_string (Print.eval_string result); print_newline()
  | NoneT -> print_string ("NotEval: " ^ Print.eval_string parse); print_newline ()


let rec get () =
  let getin () =
  let lexbuf = Lexing.from_channel stdin in
    write lexbuf; get ()
  in
  try getin ()
  with
      Lexer.Error m  -> print_string m; print_newline(); get() 
    | Parser.Error -> print_string "Parser Error"; print_newline(); get()


let readfile () = 
      let file = Sys.argv.(1) in
      let oc   = open_in file in
      let rec loop () = 
        let rec ww () =
            let line = input_line oc in
            let lexbuf = Lexing.from_string line in 
            write lexbuf; ww ()
          in
          try ww ()
          with
            End_of_file     -> close_in oc
          | Lexer.Error mes -> print_string mes; print_newline(); loop ()
          | Parser.Error    -> print_string "Parser Error"; print_newline(); loop () in
      loop ()

let () =
  match (Array.length Sys.argv) with
    1 -> get ()
  | _ -> readfile ()

