{
  exception Error of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }
| "("   { Parser.LPAREN }
| ")"   { Parser.RPAREN }
| ";"   { Parser.SEMI }
| "\."   { Parser.ABS }
| "Ap"   { Parser.APP }
| ['0'-'9'] {Parser.VAR (int_of_string (Lexing.lexeme lexbuf))}
| eof   { exit 0 }
| _     { raise (Error (Printf.sprintf "At offset %d: unexpected character." (Lexing.lexeme_start lexbuf))) }

