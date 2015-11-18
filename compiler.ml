(* compiler.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2015
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  let rec loop s n =
    match s with
    | [] -> String.make n '?'
    | car :: cdr ->
       let result = loop cdr (n + 1) in
       String.set result n car;
       result
  in
  loop s 0;;

type fraction = {numerator : int; denominator : int};;

type number =
  | Int of int
  | Fraction of fraction;;

type sexpr =
  | Void
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

module type SEXPR = sig
  val sexpr_to_string : sexpr -> string
end;; (* signature SEXPR *)

module Sexpr : SEXPR = struct
  
exception X_invalid_fraction of fraction;;

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (Char.lowercase ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let sexpr_to_string sexpr = raise X_not_yet_implemented;;

end;; (* struct Sexpr *)

module type PARSER = sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end;;

module Parser : PARSER = struct

open PC;;


(* parsers for Comments & Whitespaces *)
let nt_star_whitespace = star nt_whitespace;;
let nt_semicolon = char ';';;
let nt_hashtag = char '#';;
let no_return_func = fun e -> "";;

let nt_line_comment = 
	let nt_new_line = char '\n' in 
	let nt_all_symbols = const (fun ch -> true) in 
	let nt_comment = diff nt_all_symbols nt_new_line in 
	let nt_comment = star nt_comment in 
	let nt_comment = nt_comment in 
	let nt_comment = caten nt_semicolon nt_comment in 
	  pack nt_comment no_return_func;;

let nt_sexpr_comment = 
	let nt_start_of_comment = caten nt_hashtag nt_semicolon in 
	let nt_comment = caten nt_start_of_comment nt_sexpr in 
	  pack nt_comment no_return_func;;

let nt_comments_and_whitespaces = raise X_not_yet_implemented;;




let read_sexpr string = raise X_not_yet_implemented;;

let read_sexprs string = raise X_not_yet_implemented;;

end;; (* struct Parser *)

(* work on the tag parser starts here *)

type expr =
  | Const of sexpr
  | Var of string
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list)
  | ApplicTP of expr * (expr list);;

exception X_syntax_error;;

module type TAG_PARSER = sig
  val read_expression : string -> expr
  val read_expressions : string -> expr list
  val expression_to_string : expr -> string
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "do"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

let rec process_scheme_list s ret_nil ret_one ret_several =
  match s with
  | Nil -> ret_nil ()
  | (Pair(sexpr, sexprs)) ->
     process_scheme_list sexprs
			 (fun () -> ret_one sexpr)
			 (fun sexpr' -> ret_several [sexpr; sexpr'])
			 (fun sexprs -> ret_several (sexpr :: sexprs))
  | _ -> raise X_syntax_error;;
  
let scheme_list_to_ocaml_list args = 
  process_scheme_list args
		      (fun () -> [])
		      (fun sexpr -> [sexpr])
		      (fun sexprs -> sexprs);;
    
let expand_let_star ribs sexprs =
  let ribs = scheme_list_to_ocaml_list ribs in
  let params = List.map (function
			  | (Pair(name, (Pair(expr, Nil)))) -> name
			  | _ -> raise X_this_should_not_happen) ribs in
  let args = List.map
	       (function
		 | (Pair(name, (Pair(expr, Nil)))) -> expr
		 | _ -> raise X_this_should_not_happen) ribs in
  let params_set = List.fold_right
		     (fun a s ->
		      if (ormap
			    (fun b ->
			     (match (a, b) with
			      | (Symbol a, Symbol b) -> a = b
			      | _ -> raise X_this_should_not_happen))
			    s)
		      then s else a :: s)
		     params
		     [] in
  let place_holders = List.fold_right
			(fun a s -> Pair(a, s))
			(List.map
			   (fun var -> (Pair(var, (Pair((Bool false), Nil)))))
			   params_set)
			Nil in
  let assignments = List.map2
		      (fun var expr ->
		       (Pair((Symbol("set!")),
			     (Pair(var, (Pair(expr, Nil)))))))
		      params args in
  let body = List.fold_right
	       (fun a s -> Pair(a, s))
	       assignments
	       sexprs in
  (Pair((Symbol("let")), (Pair(place_holders, body))));;

let expand_letrec ribs sexprs =
  let ribs = scheme_list_to_ocaml_list ribs in
  let params = List.map (function
			  | (Pair(name, (Pair(expr, Nil)))) -> name
			  | _ -> raise X_this_should_not_happen) ribs in
  let args = List.map
	       (function
		 | (Pair(name, (Pair(expr, Nil)))) -> expr
		 | _ -> raise X_this_should_not_happen) ribs in
  let ribs = List.map
	       (function
		 | (Pair(name, (Pair(expr, Nil)))) ->
		    (Pair(name, (Pair(Bool false, Nil))))
		 | _ -> raise X_this_should_not_happen)
	       ribs in
  let body = List.fold_right
	       (fun a s -> Pair(a, s))
	       (List.map2
		  (fun var expr ->
		   (Pair((Symbol("set!")),
			 (Pair(var, (Pair(expr, Nil)))))))
		  params args)
	       sexprs in
  let ribs = List.fold_right
	       (fun a s -> Pair(a, s))
	       ribs
	       Nil in
  (Pair((Symbol("let")), (Pair(ribs, body))));;

exception X_unquote_splicing_here_makes_no_sense;;

let rec expand_qq sexpr = match sexpr with
  | (Pair((Symbol("unquote")), (Pair(sexpr, Nil)))) -> sexpr
  | (Pair((Symbol("unquote-splicing")), (Pair(sexpr, Nil)))) ->
     raise X_unquote_splicing_here_makes_no_sense
  | (Pair(a, b)) ->
     (match (a, b) with
      | ((Pair((Symbol("unquote-splicing")), (Pair(a, Nil)))), b) ->
	 let b = expand_qq b in
	 (Pair((Symbol("append")),
	       (Pair(a, (Pair(b, Nil))))))
      | (a, (Pair((Symbol("unquote-splicing")), (Pair(b, Nil))))) ->
	 let a = expand_qq a in
	 (Pair((Symbol("cons")), (Pair(a, (Pair(b, Nil))))))
      | (a, b) ->
	 let a = expand_qq a in
	 let b = expand_qq b in
	 (Pair((Symbol("cons")), (Pair(a, (Pair(b, Nil)))))))
  | (Vector(sexprs)) ->
     let s = expand_qq (List.fold_right (fun a b -> Pair(a, b)) sexprs Nil) in
     (Pair((Symbol("list->vector")), (Pair(s, Nil))))
  | Nil | Symbol _ -> (Pair((Symbol("quote")), (Pair(sexpr, Nil))))
  | expr -> expr;;

let tag_parse sexpr = raise X_not_yet_implemented;;

let read_expression string = tag_parse (Parser.read_sexpr string);;

let read_expressions string = List.map tag_parse (Parser.read_sexprs string);;

let expression_to_string expr = raise X_not_yet_implemented;;
  
end;; (* struct Tag_Parser *)

let test_parser string =
  let expr = Tag_Parser.read_expression string in
  let string' = (Tag_Parser.expression_to_string expr) in
  Printf.printf "%s\n" string';;
