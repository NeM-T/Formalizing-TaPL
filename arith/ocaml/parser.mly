%{
  open Eval
%}


%token LPAREN RPAREN SEMI
%token PRED
%token SUCC
%token IF THEN ELSE IFO ZERO TRUE FALSE 

%start toplevel
%type <Eval.term> toplevel
%%

toplevel :
  e=Expr SEMI {e}

Expr :
  e=If0Expr {e}
  | e=PExpr {e}

PExpr :
  PRED e=PExpr {Pred e}
  | e=SEexpr {e}

SEexpr :
  SUCC e=PExpr {Succ e}
  | e=VExpr {e}

VExpr :
  TRUE    {Tru}
  | FALSE {Fls}
  | ZERO  {O}
  | LPAREN e=Expr RPAREN {e}

If0Expr :
  IFO e=Expr {Iszero e}
  | e=IfExpr  {e}

IfExpr :
  IF c=Expr THEN t=Expr ELSE f=Expr {If (c, t, f)}

