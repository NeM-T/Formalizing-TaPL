%{
  open Eval

  let rec change n =
    match n with
    | 0 -> O
    | _ -> S (change (n - 1))
%}


%token LPAREN RPAREN SEMI
%token APP
%token ABS 
%token <int> VAR

%start toplevel
%type <Eval.term> toplevel
%%

toplevel :
  e=Expr SEMI {e}

Expr :
  APP t1=Expr t2=Expr  {App (t1, t2)}
  | e=AExpr {e}

AExpr :
  ABS e=Expr {Abs e}
  | e=VExpr {e}

VExpr :
  n = VAR  {Var (change n)}
  | LPAREN e=Expr RPAREN {e}
