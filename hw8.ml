(** Exercise 1: Parse a Tree *)
let parse_tree_tests : (string * tree option) list = [
  ("", None);
  ("((. < 5 > .) < 4 > .)", Some (Node (Node (Leaf, 5, Leaf), 4, Leaf)))
]

let rec tree_parser i =
  let open Parser in
  let tree_parser_impl =
    first_of_2
      (const_map Leaf (symbol "."))
      ((** What should we do to parse a [Node] tree? *) 
        (symbol "(") |*> (fun _ ->
            tree_parser |*> (fun x -> 
                (skip (symbol "<")) |*> (fun _ ->
                    int_digits |*> (fun y ->
                        (skip (symbol ">")) |*> (fun _ -> 
                            tree_parser |*> (fun z -> 
                                symbol ")" |*> ((fun _ ->
                                    of_value (Node (x, y, z))
                                  ))))))))
            
      )
  in
  tree_parser_impl i

(** DO NOT Change This Definition *)
let parse_tree : string -> tree option =
  let open Parser in
  run (between spaces eof tree_parser)

(** Part 1: Parse an Arithmetic Expression *)
let parse_arith_tests : (string * arith option) list = [
  ("", None);
  ("5 + 4", Some (Bop (Const 5, Plus, Const 4)))
]

let rec arith_parser i =
  let open Parser in
  let atomic_exp_parser =
    (** You may need to use [arith_parser] here *) 
    first_of_2
      (map (fun n -> Const n) int_digits)
      (
        between
          (symbol "(")
          (symbol ")")
          (arith_parser)
      )
  in
  let power_exp_parser =
    right_assoc_op (symbol "^" |*> fun _ -> of_value Power) 
      atomic_exp_parser
      (fun l op r -> Bop (l, op, r))
  in
  let multiplicative_exp_parser =
    left_assoc_op (symbol "*" |*> fun _ -> of_value Times) 
      power_exp_parser
      (fun l op r -> Bop (l, op, r))
  in
  let arith_exp_parser_impl =
    left_assoc_op 
      (
        first_of_2
          (symbol "+" |*> fun _ -> of_value Plus)
          (symbol "-" |*> fun _ -> of_value Minus)
      )
      multiplicative_exp_parser
      (fun l op r -> Bop (l, op, r))
  in
  arith_exp_parser_impl i

(** DO NOT Change This Definition *)
let parse_arith : string -> arith option =
  let open Parser in
  run (between spaces eof arith_parser)
