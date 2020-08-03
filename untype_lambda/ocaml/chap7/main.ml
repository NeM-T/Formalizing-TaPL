open Lambda
open Eval
open Print

let test =
  (* (λ x. x)  λ y. y => λ y. y *)
  (App(Abs(['x'], Var(nat_of_int 0, nat_of_int 1)), Abs(['y'], Var(nat_of_int 0, nat_of_int 1)))) ::

  (* (λ x. λ y. x) λ z. z => λ y. λ z. z *)
  (App(Abs(['x'], Abs(['y'], Var(nat_of_int 1, nat_of_int 2))), Abs(['z'], Var(nat_of_int 0, nat_of_int 1)))) ::

  (* (λ x. λ x'. x) (λ x. x) => λ x'. λ x. x *)
  (App(Abs(['x'], Abs(['x'], Var(nat_of_int 1, nat_of_int 2))), Abs(['x'], Var(nat_of_int 0, nat_of_int 1)))) ::

  (* (λ x. λ y. x) (λ z. z) (λ w. w) => (λ y. λ z. z) (λ w. w) *)
  (App(App(Abs(['x'], Abs(['y'], Var(nat_of_int 1, nat_of_int 2))), Abs(['z'], Var(nat_of_int 0, nat_of_int 1))), Abs(['w'], Var(nat_of_int 0, nat_of_int 1)))) ::

  (* (λ x. x) ((λ y. y) (λ z. z))  => (λ x. x) (λ z. z) *)
  (App(Abs(['x'], Var(nat_of_int 0, nat_of_int 1)), App(Abs(['y'], Var(nat_of_int 0, nat_of_int 1)), Abs(['z'], Var(nat_of_int 0, nat_of_int 1))))) ::

  (* (λ x. x x) (λ x. x x) => (λ x. x x) (λ x. x x) *)
  (App(Abs(['x'], App(Var(nat_of_int 0, nat_of_int 1), Var(nat_of_int 0, nat_of_int 1))), Abs(['x'], App(Var(nat_of_int 0, nat_of_int 1), Var(nat_of_int 0, nat_of_int 1))))) ::
  []

let () =
  let rec print_result li =
    match li with
    | [] -> ()
    | t :: li' ->
        print_string (string_of_chars (printtm [] t)); print_string "ーー＞";
        print_string (string_of_chars(test_eval t)); 
        print_newline();
        print_result li'
  in
  print_result test

