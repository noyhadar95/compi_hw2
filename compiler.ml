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

  
let rec sexpr_to_string_helper sexpr = 
	match sexpr with 
	| Void -> raise X_this_should_not_happen
	| Bool e -> if e=true then "#t" else "#f"
	| Nil -> "()"
	| Number (Int n) -> string_of_int n
	| Number (Fraction {numerator = numer; denominator = denom}) -> (string_of_int numer) ^ "/" ^ (string_of_int denom)
	| Char c -> (match (Char.code c) with 
					| 10 -> "#\\newline"
					| 13 -> "#\\return"
					| 9 -> "#\\tab"
					| 12 -> "#\\page"
					| 32 -> "#\\space"
					| _ -> "#\\" ^ (String.make 1 c))
	| String str -> "\"" ^ str ^ "\""
	| Symbol s -> s
	| Pair(e1, Nil) -> "(" ^ (sexpr_to_string_helper e1) ^ ")"
	| Pair(Symbol name, Pair(e1, Nil)) -> (match name with 
					| "quote" -> "'" ^ (sexpr_to_string_helper e1)
					| "quasiquote" -> "`" ^ (sexpr_to_string_helper e1)
					| "unquote-splicing" -> ",@" ^ (sexpr_to_string_helper e1)
					| "unquote" -> "," ^ (sexpr_to_string_helper e1)
					| _ -> let e2 = Pair(e1, Nil) in 
							"(" ^ (sexpr_to_string_helper e1) ^ " " ^ (sexpr_to_string_helper e2) ^ ")")
	| Pair(e1, e2) -> "(" ^ (sexpr_to_string_helper e1) ^ " " ^ (sexpr_to_string_helper e2) ^ ")"
	| Vector es -> "#(" ^ (List.fold_right (fun s1 s2 -> s1^" "^s2) (List.map sexpr_to_string_helper es) "") ^ ")";;
	
let sexpr_to_string sexpr = sexpr_to_string_helper sexpr;;
	

end;; (* struct Sexpr *)

module type PARSER = sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end;;

module Parser : PARSER = struct

open PC;;

let car = (fun (a,b) -> a);;
let cdr = (fun (a,b) -> b);;
let nt_left_par = char '(';;
let nt_right_par = char ')';;
let nt_semicolon = char ';';;
let nt_hashtag = char '#';;

let empty_str_func = fun e -> "";;
(* gcd function definition *)
let rec gcd a b =
    if b = 0 then a 
	else gcd b (a mod b);;

let nt_letters_ci = range_ci 'a' 'z';;
let nt_slash = char '/';;
let nt_back_slash = char '\\';;



let make_char_value base_char displacement =
  let base_char_value = Char.code base_char in
  fun ch -> (Char.code ch) - base_char_value + displacement;;
let nt_digit_0_9 = pack (range '0' '9') (make_char_value '0' 0);;
let nt_digit_1_9 = pack (range '1' '9') (make_char_value '0' 0);;
let nt_nat =
  let nt = nt_digit_0_9 in
  let nt = star nt in
  let nt = pack nt (fun s -> List.fold_left (fun a b -> a * 10 + b) 0 s) in
  let nt' = char '0' in
  let nt'' = char '0' in
  let nt''' = range '0' '9' in
  let nt'' = caten nt'' nt''' in
  let nt' = diff nt' nt'' in
  let nt' = pack nt' (fun e -> 0) in
  let nt = disj nt nt' in
  nt;;
let nt_hex_unsigned = 
	let nt_a_f_ci = range_ci 'a' 'f' in 
	let displacement = - (Char.code 'a') + (Char.code '9') + 1 in 
	let nt_a_f_ci = pack nt_a_f_ci (make_char_value '0' displacement) in
	let nt = nt_digit_0_9 in
	let nt = disj nt nt_a_f_ci in 
	let nt = star nt in
	let nt = pack nt (fun s -> List.fold_left (fun a b -> a * 16 + b) 0 s) in
	let nt' = char '0' in
	let nt'' = char '0' in
	let nt''' = disj (range '0' '9') (range_ci 'a' 'f') in
	let nt'' = caten nt'' nt''' in
	let nt' = diff nt' nt'' in
	let nt' = pack nt' (fun e -> 0) in
	let nt = disj nt nt' in
	let nt_0 = char '0' in 
	let nt_x = char_ci 'x' in
	let nt_0x = caten nt_0 nt_x in
	let nt = caten nt_0x nt in
	let nt = pack nt cdr in
	  nt;;
let nt_hex_signed = 
	let nt = char '-' in
	let nt = pack nt (fun e -> -1) in
	let nt' = char '+' in
	let nt' = pack nt' (fun e -> 1) in
	let nt = disj nt nt' in
	let nt = maybe nt in
	let nt = pack nt (function | None -> 1 | Some(mult) -> mult) in
	let nt_hex_num = caten nt nt_hex_unsigned in
	let nt_hex_num = pack nt_hex_num (fun (mult, n) -> (mult * n)) in
	  nt_hex_num;;
let nt_int =
  let nt = char '-' in
  let nt = pack nt (fun e -> -1) in
  let nt' = char '+' in
  let nt' = pack nt' (fun e -> 1) in
  let nt = disj nt nt' in
  let nt = maybe nt in
  let nt = pack nt (function | None -> 1 | Some(mult) -> mult) in 
  let nt' = range '0' '9' in
  let nt' = pack nt' (make_char_value '0' 0) in
  let nt' = plus nt' in
  let nt' = pack nt' (fun s -> List.fold_left (fun a b -> a * 10 + b) 0 s) in
  let nt = caten nt nt' in
  let nt = pack nt (fun (mult, n) -> (mult * n)) in
  nt;;
let nt_integer_hex = pack (disj nt_hex_signed nt_int) (fun e -> Int e);;
let nt_fraction = 
	let nt_numerator = disj nt_hex_signed nt_int in 
	let nt_numerator_slash = caten nt_numerator nt_slash in 
	let nt_numerator_slash = pack nt_numerator_slash car in 
	let nt_denominator = disj nt_hex_unsigned nt_nat in
	let nt_denominator = guard nt_denominator (fun num -> num<>0) in
	let nt_frac = caten nt_numerator_slash nt_denominator in 
	let nt_frac = pack nt_frac (fun (numer, denom) -> 
									let gcd = gcd numer denom in 
										(numer/gcd, denom/gcd)) in 
	  pack nt_frac (fun (numer, denom) -> if (numer mod denom)=0 then (Int (numer/denom)) 
										else Fraction {numerator=numer; denominator=denom});;

	
let nt_punctuation = one_of "!$^*-_=+<>/?";;


let nt_bad_number = 
	let nt_fraction = 
		let nt_numerator = disj nt_hex_signed nt_int in 
		let nt_numerator_slash = caten nt_numerator nt_slash in 
		let nt_numerator_slash = pack nt_numerator_slash car in 
		let nt_denominator = disj nt_hex_unsigned nt_nat in
		let nt_denominator = guard nt_denominator (fun num -> num<=0) in
		let nt_frac = caten nt_numerator_slash nt_denominator in 
		let nt_frac = pack nt_frac (fun (numer, denom) -> 
									let gcd = gcd numer denom in 
										(numer/gcd, denom/gcd)) in 
		pack nt_frac (fun (numer, denom) -> if (numer mod denom)=0 then (Int (numer/denom)) 
										else Fraction {numerator=numer; denominator=denom}) in 
		nt_fraction;;

	


(* parsers for concrete syntax of sexprs *)
let nt_bool = 
	let nt_true = caten nt_hashtag (char_ci 't') in 
	let nt_true = pack nt_true (fun e -> Bool true) in 
	let nt_false = caten nt_hashtag (char_ci 'f') in 
	let nt_false = pack nt_false (fun e -> Bool false) in 
	  disj nt_true nt_false ;;

let rec nt_number str = 
	let nt = disj (pack nt_fraction (fun e -> Number e)) 
				(pack nt_integer_hex (fun e -> Number e)) in
	diff nt (caten nt nt_symbol) str
		 
and nt_symbol str = 
	let nt_letters_ci_packed = pack nt_letters_ci (fun ch -> String.make 1 (Char.lowercase ch)) in 
	let nt_digit_0_9_packed = pack nt_digit_0_9 (fun n -> string_of_int n) in 
	let nt_punctuation_packed = pack nt_punctuation (fun ch -> String.make 1 ch) in 
	let nt = disj_list [nt_letters_ci_packed; nt_digit_0_9_packed; nt_punctuation_packed] in 
	let nt = plus nt in
	let nt = pack nt (fun str_list -> List.fold_right (^) str_list "") in
	let nt = pack nt (fun s -> Symbol s) in
	  diff nt nt_number str ;;

			
	let nt_string = 
		let nt_string_meta_chars = 
			let nt_newline = (pack (word "\\n") (fun _ -> '\n')) in 
			let nt_return = (pack (word "\\r") (fun _ -> '\r')) in 
			let nt_tab = (pack (word "\\t") (fun _ -> '\t')) in 
			let nt_page = (pack (word "\\f") (fun _ -> (Char.chr 12))) in 
			let nt_backslash = (pack (word "\\\\") (fun _ -> '\\')) in 
			let nt_double_quote = (pack (word "\\\"") (fun _ -> '\"')) in 
			disj_list [nt_newline;
						nt_return;
						nt_tab;
						nt_page;
						nt_backslash;
						nt_double_quote] in 
		let nt_string_content = diff nt_any (one_of "\\\"") in 
		let nt_string_content = star (disj nt_string_content nt_string_meta_chars) in 
		let nt_string_content = pack nt_string_content (fun e -> String (List.fold_right (^) 
																					(List.map (fun ch -> String.make 1 ch)
																								e)
																					"")) in 
		let nt_double_quote = char '"' in
		let nt = caten nt_double_quote nt_string_content in 
		let nt = pack nt cdr in 
		let nt = caten nt nt_double_quote in 
		let nt = pack nt car in 
		  nt ;;
		  
let nt_char = 
	let nt_visible_range_char = const (fun ch -> (Char.code ch) > 32) in 
	let nt_named_chars = disj_list [pack (word_ci "newline") (fun s -> Char.chr 10);
									pack (word_ci "return") (fun s -> Char.chr 13);
									pack (word_ci "tab") (fun s -> Char.chr 9);
									pack (word_ci "page") (fun s -> Char.chr 12);
									pack (word_ci "space") (fun s -> Char.chr 32)] in 
	let nt_prefix = caten nt_hashtag nt_back_slash in
	let nt = disj nt_named_chars nt_visible_range_char in 
	let nt = caten nt_prefix nt in 
	let nt = pack nt cdr in 
	let nt = pack nt (fun ch -> Char ch) in 
	  nt ;;
		
	  
let rec nt_vector str = 
		let nt = star nt_sexpr in
		let nt = pack nt (fun es -> Vector es) in
		let nt' = caten nt_hashtag nt_left_par in 
		let nt = caten nt' nt in 
		let nt = pack nt cdr in 
		let nt = caten nt nt_right_par in
		let nt = pack nt car in 
		  nt str
		  
and nt_pair str = 
		let nt_proper_list = 
			let nt = star nt_sexpr in
			let nt = pack nt (fun es -> List.fold_right (fun a b -> Pair (a, b)) es Nil) in
			let nt = caten nt_left_par nt in 
			let nt = pack nt cdr in 
			let nt = caten nt nt_right_par in
			let nt = pack nt car in 
			  nt in
		let nt_improper_list = 
			let nt = plus nt_sexpr in
			let nt = caten nt_left_par nt in 
			let nt = pack nt cdr in 
			let nt' = char '.' in
			let nt = caten nt nt' in
			let nt = pack nt car in
			let nt = caten nt nt_sexpr in
			let nt = pack nt (fun (e1,e2) -> e1@[e2]) in
			let nt = pack nt (fun es -> List.fold_right (fun a b -> Pair (a, b)) es Nil) in
			let nt = caten nt nt_right_par in
			let nt = pack nt car in 
			  nt in
		  disj nt_proper_list nt_improper_list str
		  
and nt_quote_like_forms str = 
		let nt_quoted = caten (char '\'') nt_sexpr in
		let nt_quoted = pack nt_quoted (fun (ch,e) ->Pair (Symbol "quote", Pair (e,Nil))) in 
		let nt_qquoted = caten (char '`') nt_sexpr in
		let nt_qquoted = pack nt_qquoted (fun (ch,e) ->Pair (Symbol "quasiquote", Pair (e,Nil))) in
		let nt_unquoted_spliced = caten (word ",@") nt_sexpr in
		let nt_unquoted_spliced = pack nt_unquoted_spliced (fun (str,e) ->Pair (Symbol "unquote-splicing", Pair (e,Nil))) in
		let nt_unquoted = caten (char ',') nt_sexpr in
		let nt_unquoted = pack nt_unquoted (fun (ch,e) ->Pair (Symbol "unquote", Pair (e,Nil))) in 
		  disj_list [nt_quoted; nt_qquoted; nt_unquoted_spliced; nt_unquoted] str

(* parser for Comments & Whitespaces *) 		  
and nt_comments_and_whitespaces str = 
		let nt_line_comment = 
			let nt_new_line = char '\n' in 
			let nt_comment = diff nt_any nt_new_line in 
			let nt_comment = star nt_comment in 
			let nt_comment = caten nt_semicolon nt_comment in 
			let nt_comment = caten nt_comment (disj (pack nt_end_of_input empty_str_func) (pack nt_new_line empty_str_func)) in 
			  pack nt_comment empty_str_func in
		let nt_sexpr_comment = 
			let nt_start_of_comment = word "#;" in 
			let nt_comment = caten nt_start_of_comment nt_sexpr in 
			  pack nt_comment empty_str_func in
		let nt_whitespace_packed = pack nt_whitespace empty_str_func in
		  star (disj_list [nt_whitespace_packed; nt_line_comment; nt_sexpr_comment]) str

and nt_nil str = 
		let nt = caten nt_left_par nt_comments_and_whitespaces in
		let nt = caten nt nt_right_par in
		let nt = pack nt (fun e -> Nil) in
		  nt str

and nt_sexpr str = 
	let nt_disj_sexpr = 
		disj_list [nt_bool;
					nt_nil;
					nt_number;
					nt_symbol;
					nt_char;
					nt_string;
					nt_vector;
					nt_pair;
					nt_quote_like_forms] in
	let nt_sexpr_with_comments = caten nt_comments_and_whitespaces nt_disj_sexpr in 
	let nt_sexpr_with_comments = pack nt_sexpr_with_comments cdr in
	let nt_sexpr_with_comments = caten nt_sexpr_with_comments nt_comments_and_whitespaces in 
	let nt_sexpr_with_comments = pack nt_sexpr_with_comments car in
	  nt_sexpr_with_comments str;;
	

	
	
let read_sexpr string = 
	let ch_list = string_to_list string in 
	let (sexpr, res_ch_list) = nt_sexpr ch_list in
	  sexpr;;

let rec read_sexprs_helper = 
	function
	| "" -> []
	| str -> let (e, s) = (nt_sexpr (string_to_list str)) in
				[e] @ (read_sexprs_helper (list_to_string s));;
	  
let read_sexprs string = 
	read_sexprs_helper string;;

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


 (* tag parser helper functions *)

let rec process_scheme_improper_list s ret_nil ret_one ret_several =
  match s with
  | Symbol name -> (String name)::(ret_nil ())
  | (Pair(sexpr, sexprs)) ->
     process_scheme_list sexprs
			 (fun () -> ret_one sexpr)
			 (fun sexpr' -> ret_several [sexpr; sexpr'])
			 (fun sexprs -> ret_several (sexpr :: sexprs))
  | _ -> raise X_syntax_error;;
  
(* return a list of the form (opt_param :: paras_str_list) *)
let scheme_improper_list_to_ocaml_list args = 
  process_scheme_improper_list args
		      (fun () -> [])
		      (fun sexpr -> [sexpr])
		      (fun sexprs -> sexprs);;
	
let rec is_proper_list = 
	function
	| Nil -> true
	| (Pair(sexpr, sexprs)) -> is_proper_list sexprs
	| _ -> false;;
	

let rec improper_list_to_tuple im_list list_acc = 
	match im_list with
	| Symbol name -> (list_acc, name)
	| (Pair(sexpr, sexprs)) -> improper_list_to_tuple sexprs (list_acc@[sexpr])
	| _ -> raise X_syntax_error;;
	

let param_proper_list_to_str_list p_list=
	let param_ocaml_list = (scheme_list_to_ocaml_list p_list) in
	List.map (function
			  | Symbol(param_name) -> param_name
			  | _ -> raise X_this_should_not_happen) 
			param_ocaml_list;;
			
(* return a list of the form (opt_param, paras_str_list) *)
let param_improper_list_to_str_list p_list=
	let (param_ocaml_list, opt_param) = (improper_list_to_tuple p_list []) in
	let mapped_params = List.map (function
								  | Symbol(param_name) -> param_name
								  | _ -> raise X_this_should_not_happen) 
								param_ocaml_list in
	(mapped_params, opt_param);;
	

let not_exists el list = 
	if (andmap (fun a -> a<>el) list) then true
	else false;;
	

let expand_and sexprs =
  let sexprs_ocaml_list = scheme_list_to_ocaml_list sexprs in
  let list_without_last = List.rev (List.tl (List.rev sexprs_ocaml_list)) in
  let last_of_list = List.hd (List.rev sexprs_ocaml_list) in
  let not_sexprs = List.map
	       (fun sexpr -> (Pair((Symbol("not")), (Pair(sexpr, Nil))))) 
		   list_without_last in
  let not_sexprs = not_sexprs@[last_of_list] in
  let body = List.fold_right
	       (fun a b -> Pair(a, b))
	       not_sexprs
	       Nil in
  (Pair((Symbol("or")), body));;
	
(* tag parser helper functions end *)
  
let rec tag_parse_helper sexpr = 
	match sexpr with
	| Void -> raise X_this_should_not_happen
	| Bool e -> Const (Bool e)
	| Nil -> Const Nil
	| Number (Int n) -> Const (Number (Int n))
	| Number (Fraction {numerator = numer; denominator = denom}) -> Const (Number (Fraction {numerator = numer; denominator = denom}))
	| Char c -> Const (Char c)
	| String str -> Const (String str)
	| (Pair((Symbol("quote")), (Pair(field, Nil)))) -> Const field
	| (Symbol(sym)) when not_exists sym reserved_word_list -> Var sym (* !!!!!!!!!!make sure the when is needed*)(*symbol var*)
	| (Pair((Symbol("unquote")), (Pair((Symbol(sym)), Nil)))) when not_exists sym reserved_word_list  -> Var sym (*unquoted var*)
	| (Pair((Symbol("if")), (Pair(test, (Pair(dit, (Pair(dif, Nil)))))))) -> (*if then else*)
		If ((tag_parse_helper test), (tag_parse_helper dit), (tag_parse_helper test))
	| (Pair((Symbol("if")), (Pair(test, (Pair(dit, Nil)))))) -> (*if then*)
		If ((tag_parse_helper test), (tag_parse_helper dit), Const(Void))
	| (Pair((Symbol("lambda")), (Pair(params, (Pair(body, Nil)))))) -> (*lambda types*)
		(match params with
		| Nil -> LambdaSimple ([], tag_parse_helper body)
		| Pair(_) -> 
			if is_proper_list params then 
				let param_str_list = param_proper_list_to_str_list params in
				LambdaSimple (param_str_list, tag_parse_helper body) (*lambda simple*)
			else let (param_str_list, opt_param) = param_improper_list_to_str_list params in
				LambdaOpt(param_str_list, opt_param, tag_parse_helper body) (*lambda opt*)
		| Symbol(opt_param)-> LambdaOpt([], opt_param, tag_parse_helper body) (*lambda variadic*)
		| _ -> raise X_syntax_error)
	| (Pair((Symbol("or")), args)) -> (*or*)
		(match args with
		| Nil ->  Or []
		| (Pair(_, _)) -> 
			let args_ocaml_list = (scheme_list_to_ocaml_list args) in
			let mapped_args = List.map tag_parse_helper args_ocaml_list in
			Or mapped_args
		| _ -> raise X_syntax_error)
	| (Pair((Symbol("and")), args)) -> (*and*)
		(match args with
		| Nil -> tag_parse_helper (Pair((Symbol("or")), (Pair((Bool true), Nil))))
		| (Pair(_, _)) -> tag_parse_helper (expand_and args)
		| _ -> raise X_syntax_error)
	| (Pair((Symbol("define")), (Pair(name, (Pair(expr, Nil)))))) -> (*define*)
		let var = (match name with
				| Symbol sym -> Var sym
				| _ -> raise X_syntax_error) in
		let value = (tag_parse_helper expr) in
		Def (var, value)
	
	| (Pair(op, args)) -> (*application*)
		(match args with
		| Nil ->  Applic (tag_parse_helper op , [])
		| (Pair(_, _)) -> 
			let args_ocaml_list = (scheme_list_to_ocaml_list args) in
			let mapped_args = List.map tag_parse_helper args_ocaml_list in
			Applic (tag_parse_helper op , mapped_args)
		| _ -> raise X_syntax_error
		);;


	| Pair(Symbol name, Pair(e1, Nil)) -> (match name with 
					| "quote" -> "'" ^ (sexpr_to_string_helper e1)
					| "quasiquote" -> "`" ^ (sexpr_to_string_helper e1)
					| "unquote-splicing" -> ",@" ^ (sexpr_to_string_helper e1)
					| "unquote" -> "," ^ (sexpr_to_string_helper e1)
					| _ -> let e2 = Pair(e1, Nil) in 
							"(" ^ (sexpr_to_string_helper e1) ^ " " ^ (sexpr_to_string_helper e2) ^ ")")
	| Vector es -> "#(" ^ (List.fold_right (fun s1 s2 -> s1^" "^s2) (List.map sexpr_to_string_helper es) "") ^ ")";;


(* tag_parse : sexpr -> expr *)
let tag_parse sexpr = 
	tag_parse_helper sexpr;;

let read_expression string = tag_parse (Parser.read_sexpr string);;

let read_expressions string = List.map tag_parse (Parser.read_sexprs string);;

let expression_to_string expr = raise X_not_yet_implemented;;
  
end;; (* struct Tag_Parser *)

let test_parser string =
  let expr = Tag_Parser.read_expression string in
  let string' = (Tag_Parser.expression_to_string expr) in
  Printf.printf "%s\n" string';;
