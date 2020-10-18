open Format
open Constr
open Term
open Context

let print_array f sep fin fmt a =
  Array.iter (fun i -> fprintf fmt "%a%s" f i sep) a;
  fprintf fmt "%s@." fin

let string_of_name name =
  match name with
    | Names.Anonymous -> "anonymous"
    | Names.Name n -> Names.Id.to_string n

let print_kn fmt kn =
  fprintf fmt "%s" (Names.Constant.to_string (Names.Constant.make1 kn))

let coq_init_constant s =
  Coqlib.gen_reference_in_modules "RecursiveDefinition" Coqlib.init_modules s

let coq_or = coq_init_constant "or"

let rec print_constr evd fmt (c: EConstr.t) =
  let c' = EConstr.to_constr evd c in
  let f = print_constr evd in
  match EConstr.kind evd c with
  | _ when Globnames.is_global (Coqlib.build_coq_False ()) c' -> fprintf fmt "False"
  | _ when Globnames.is_global (Coqlib.build_coq_True ()) c' -> fprintf fmt "True"
  | _ when Globnames.is_global (Coqlib.build_coq_not ()) c' -> fprintf fmt "Not"
  | _ when Globnames.is_global coq_or c' -> fprintf fmt "Or"
  | _ when Globnames.is_global (Coqlib.build_coq_and ()) c' -> fprintf fmt "And"
  | Rel i -> fprintf fmt "rel %d" i
  | Var id -> fprintf fmt ("var %s") (Names.Id.to_string id)
  | Meta _ -> fprintf fmt "meta"
  | Evar (i, constr_array) ->
      fprintf fmt "Evar : %d %a" (Evar.repr i) (print_array f " " "") constr_array
  | Sort s ->
    (match EConstr.ESorts.kind evd s with
	 | SProp -> fprintf fmt "sort(sprop)"
	 | Prop -> fprintf fmt "sort(prop)"
	 | Set -> fprintf fmt "sort(set)"
	 | Type _ -> fprintf fmt "sort(type)")
  | Cast (term, _, typ) ->
      fprintf fmt "cast du term %a avec le type %a" f term f typ
  | Prod (name, typ, typ') ->
      fprintf fmt "Prod (%s * %a * {%a})" (string_of_name name.binder_name) f typ f typ'
  | Lambda (name, typ, constr) ->
      fprintf fmt "Lambda (%s : %a=%a)"
	(string_of_name name.binder_name) f typ f constr
  | LetIn (name, constr,typ, constr') ->
      fprintf fmt "Let %s : %a = %a in %a@."
	(string_of_name name.binder_name) f typ f constr f constr'
  | App (constr, constr_array) ->
      fprintf fmt "%a @ (%a)" f constr (print_array f ", " "") constr_array
  | Const (const, _) ->
      fprintf fmt "constante %s" (Names.Constant.to_string const)
  | Ind((mult_ind, i), _) ->
      fprintf fmt "Ind (%a, %d)" print_kn (Names.MutInd.user mult_ind) i
  | Construct (((mult_ind, i), i'), _) ->
      fprintf fmt "Constructor ((%a, %d), %d)"
	print_kn (Names.MutInd.user mult_ind) i i'
  | Case (case_info, constr, constr', constr_array) ->
      fprintf fmt "match %a as %a with @.%a end" f constr f constr'
	(print_array f "\n" "") constr_array
  | Fix ((int_array, int),(name_a, type_a, constr_a)) ->
      fprintf fmt "fix %d, %d\n %a\n %a\n %a@."
	(Array.length int_array) int
	(print_array (fun fmt s ->
			fprintf fmt "%s" (string_of_name s.binder_name)) ", " "")
	name_a
	(print_array f ", " "") type_a
	(print_array f ", " "") constr_a
  | CoFix (int, (name_a, type_a, constr_a)) ->
      fprintf fmt "cofix %d\n %a\n %a\n %a@."
	int
	(print_array (fun fmt s ->
			fprintf fmt "%s" (string_of_name s.binder_name)) ", " "")
	name_a
	(print_array f ", " "") type_a
	(print_array f ", " "") constr_a
  | Proj (p, c) -> fprintf fmt "Proj (%s, %a)"
    (Names.Constant.to_string (Names.Projection.constant p)) f c
  | Int n -> fprintf fmt "Int (%s)" (Uint63.to_string n)
