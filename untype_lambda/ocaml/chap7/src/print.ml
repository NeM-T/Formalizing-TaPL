open Eval

let string_of_chars chars = 
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let rec int_of_nat = function
  | O -> 0
  | S n' -> 1 + int_of_nat n'

let rec nat_of_int n =
  match n with
  | 0 -> O
  | _ -> S (nat_of_int (n - 1))

let chars_of_string str =
  let rec walk n str l =
    match n with
    | 0 -> l
    | _ ->
        walk (n - 1) str ((String.get str n) :: l)
  in
  walk (String.length str) str []

let option_to_defalt t def =
  match t with
  | Some t' -> t'
  | None -> def
