{
  exception Error of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }
| "("   { Parser.LPAREN }
| ")"   { Parser.RPAREN }
| ";"   { Parser.SEMI }
| "O"   { Parser.ZERO }
| "S"   { Parser.SUCC }
| "Pred"{ Parser.PRED }
| "if"  { Parser.IF }
| "is0" {Parser.ISO}
| "else"{ Parser.ELSE }
| "then"{ Parser.THEN }
|"tru"  { Parser.TRUE }
|"fls"  { Parser.FALSE }
| eof   { exit 0 }
| _     { raise (Error (Printf.sprintf "At offset %d: unexpected character." (Lexing.lexeme_start lexbuf))) }

