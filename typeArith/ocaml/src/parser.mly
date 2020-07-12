%{
  open Eval
  let rec change num = 
  match num with
  | 0 -> O
  | _ -> Succ (change (num - 1))
%}

%token LPAREN RPAREN SEMI
%token PRED
%token SUCC
%token IF THEN ELSE ISO ZERO TRUE FALSE 

%token <int> NATV
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
  | n = NATV {change n} 
  | LPAREN e=Expr RPAREN {e}

If0Expr :
  ISO e=Expr {Iszero e}
  | e=IfExpr  {e}

IfExpr :
  IF c=Expr THEN t=Expr ELSE f=Expr {If (c, t, f)}

