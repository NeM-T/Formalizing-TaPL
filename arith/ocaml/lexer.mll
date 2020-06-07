{}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }
| "("   { Parser.LPAREN }
| ")"   { Parser.RPAREN }
| ";"   { Parser.SEMI }
| "O"   {Parser.ZERO}
| "S"   {Parser.SUCC}
| "Pred"{Parser.PRED}
| "if"  {Parser.IF}
| "else"{Parser.ELSE}
| "then"{Parser.THEN}
|"tru"  {Parser.TRUE}
|"fls"  {Parser.FALSE}
| eof  { exit 0 }

