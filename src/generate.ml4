(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open API
open Format
open Term
open EConstr
open Coqlib
open Tacmach
open Tacticals
open Tactics
open Pp
open Flags

open Nameops
open Entries
open Constrexpr
open Constrexpr_ops
open Topconstr
open Printing
open Ltac_plugin
open Tacinterp

DECLARE PLUGIN "containers_plugin"

type inductive_kind = Simple | Recursive | Mutual
let pr_kind = function
  | Simple -> str "Simple"
  | Recursive -> str "Recursive"
  | Mutual -> str "Mutual"

let print_id fmt id =
  fprintf fmt "%s" (Names.Id.to_string id)

let iter3 a a' a'' f =
  for i = 0 to (Array.length a - 1) do
    f i a.(i) a'.(i) a''.(i)
  done

let print_ind_body fmt ibody =
    fprintf fmt "Inductive body : {\n";
    fprintf fmt "\t name : %a\n" print_id ibody.Declarations.mind_typename;
    fprintf fmt "\t constructors : \n";
    iter3
      ibody.Declarations.mind_consnames
      ibody.Declarations.mind_nf_lc
      ibody.Declarations.mind_consnrealdecls
      (fun i id typ n -> fprintf fmt "\t #%d : %a [%d arguments] == %a\n"
	 i print_id id n print_constr typ);
    fprintf fmt "}\n"

let dl id = None, id
let cf cexpr = false, cexpr
let cprop = CAst.make @@ CSort Misctypes.GProp
let ccomparison = mkIdentC (Names.Id.of_string "comparison")
let bin_rel_t id_t =
  CAst.make @@ CProdN ([[(dl Names.Anonymous);(dl Names.Anonymous)],
		       Default Decl_kinds.Explicit, mkIdentC id_t], cprop)
let bin_cmp_t id_t =
  CProdN ([[(dl Names.Anonymous);(dl Names.Anonymous)],
		       Default Decl_kinds.Explicit, mkIdentC id_t], ccomparison)

let hole = CAst.make @@ CHole (None, Misctypes.IntroAnonymous, None)

(* à la v8.2... *)
let declare_definition
    id (loc, boxed_flag, def_obj_kind)
    binder_list red_expr_opt constr_expr
    constr_expr_opt decl_hook =
  Command.do_definition
  id (loc, false, def_obj_kind) binder_list red_expr_opt constr_expr
  constr_expr_opt decl_hook

(* building the equality predicate *)
let equiv_ref =
  Libnames.Qualid (dl (Libnames.qualid_of_string "Equivalence.equiv"))
let mk_equiv x y =
  CApp ((None, mkRefC equiv_ref),
(* 			 mkIdentC (Names.Id.of_string "equiv")), *)
	[mkIdentC x, None; mkIdentC y, None])

let rec app_expl_i acc base n =
  match n with
    | 0 -> acc
    | n ->
	let xn = Nameops.make_ident base (Some n) in
	  app_expl_i ((mkIdentC xn, None)::acc) base (n-1)

let rec prod_n_i acc n =
  match n with
    | 0 -> acc
    | n ->
	let xn = Names.Name (Nameops.make_ident "x" (Some n)) in
	let yn = Names.Name (Nameops.make_ident "y" (Some n)) in
	  prod_n_i (([dl xn; dl yn], Default Decl_kinds.Explicit, hole)::acc)
	    (n-1)

let eq_constr_i eqid cid carity =
  let xbar = app_expl_i [] "x" carity in
  let ybar = app_expl_i [] "y" carity in
  let cx = CAst.make @@ CApp ((None, mkIdentC cid), xbar) in
  let cy = CAst.make @@ CApp ((None, mkIdentC cid), ybar) in
  CAst.make @@ CProdN ((prod_n_i [] carity) @ (Util.List.init carity
				    (fun n ->
				      let xn = Nameops.make_ident "x" (Some (n+1)) in
				      let yn = Nameops.make_ident "y" (Some (n+1)) in
				      [None,Names.Anonymous],Default Decl_kinds.Explicit,
				      CAst.make @@ mk_equiv xn yn)),
	  (CAst.make @@ (CApp ((None, mkIdentC eqid), [cx, None; cy, None]))))
let make_eq_mutual ind mind body =
  let id_t = body.Declarations.mind_typename in
  let id_eq = add_suffix id_t "_eq" in
  let lconstr =
    List.map2 (fun cid carity ->
		 (cf (dl (add_suffix id_eq ("_"^(Names.Id.to_string cid))),
		      eq_constr_i id_eq cid carity)))
      (Array.to_list body.Declarations.mind_consnames)
      (Array.to_list body.Declarations.mind_consnrealdecls)
  in
    [((Loc.tag @@ id_eq, None), [], Some (bin_rel_t id_t) , lconstr), []]

(* building the ordering predicate *)
let lt_StrictOrder_ref =
  Libnames.Qualid
    (dl (Libnames.qualid_of_string "Containers.OrderedType.lt_StrictOrder"))
let mk_lt x y =
  CApp ((None, mkRefC lt_StrictOrder_ref),
	[mkIdentC x, None; mkIdentC y, None])

let lexi_constr ltid cid carity =
  let xbar = app_expl_i [] "x" carity in
  let ybar = app_expl_i [] "y" carity in
  let cx = CAst.make @@ CApp ((None, mkIdentC cid), xbar) in
  let cy = CAst.make @@ CApp ((None, mkIdentC cid), ybar) in
  let rec all_lexico_cases goal acc = function
    | 0 -> acc
    | n ->
	let xn = Nameops.make_ident "x" (Some n) in
	let yn = Nameops.make_ident "y" (Some n) in
	let base = CAst.make @@ CProdN ([[None,Names.Anonymous],
				       Default Decl_kinds.Explicit,
				       CAst.make @@ mk_lt xn yn], goal) in
	let c = CAst.make @@ CProdN (Util.List.init (n-1)
	  (fun n ->
	    let xn = Nameops.make_ident "x" (Some (n+1)) in
	    let yn = Nameops.make_ident "y" (Some (n+1)) in
	    [None,Names.Anonymous],Default Decl_kinds.Explicit, CAst.make @@ mk_lt xn yn), base) in
	let name = add_suffix ltid ("_"^(Names.Id.to_string cid)^
				      "_"^(string_of_int n)) in
	  all_lexico_cases goal ((name, c)::acc) (n-1) in
  let goal =
    CAst.make @@ CApp ((None, mkIdentC ltid), [cx, None; cy, None]) in
  let cases =
    all_lexico_cases goal [] carity in
    List.map (fun (name, c) ->
		cf (dl name,
		    CAst.make @@ CProdN ((prod_n_i [] carity), c)))
      cases

let inter_constr ltid cid carity otherids otherarities =
  let xbar = app_expl_i [] "x" carity in
  let cx = CAst.make @@ CApp ((None, mkIdentC cid), xbar) in
  let aux id ar =
    let ybar = app_expl_i [] "y" ar in
    let cy = CAst.make @@ CApp ((None, mkIdentC id), ybar) in
    let goal =
      CAst.make @@ CApp ((None, mkIdentC ltid), [cx, None; cy, None]) in
    let name =
      add_suffix ltid ("_"^(Names.Id.to_string cid)^
			 "_"^(Names.Id.to_string id)) in
    let rec prod acc v = function
      | 0 -> acc
      | n -> let xn = Names.Name (Nameops.make_ident v (Some n)) in
	  prod (([dl xn], Default Decl_kinds.Explicit, hole)::acc) v (n-1)
    in
    let foralls1 = prod [] "y" ar in
    let foralls = prod foralls1 "x" carity in
      cf (dl name, CAst.make @@ CProdN (foralls, goal))
  in
    List.map2 aux otherids otherarities

let rec lt_constr ltid names arities =
  match names, arities with
    | [], [] -> []
    | cid::otherids, carity::otherars ->
	let lexi = lexi_constr ltid cid carity in
	let inter = inter_constr ltid cid carity otherids otherars in
	  lexi@inter@(lt_constr ltid otherids otherars)
    | _, _ -> failwith "Lists should have the same lengths."

let make_lt_mutual ind mind body =
  let id_t = body.Declarations.mind_typename in
  let id_lt = add_suffix id_t "_lt" in
  let names = Array.to_list body.Declarations.mind_consnames in
  let decls = Array.to_list body.Declarations.mind_consnrealdecls in
  let lconstr = lt_constr id_lt names decls in
    [((dl id_lt, None), [], Some (bin_rel_t id_t) , lconstr), []]

(* building the comparison function *)
let ref_Eq = Libnames.Ident (dl (Names.Id.of_string "Eq"))
let ref_Lt = Libnames.Ident (dl (Names.Id.of_string "Lt"))
let ref_Gt = Libnames.Ident (dl (Names.Id.of_string "Gt"))
let id_Eq = Names.Id.of_string "Eq"
let id_Lt = Names.Id.of_string "Lt"
let id_Gt = Names.Id.of_string "Gt"

let compare_ref =
  Libnames.Qualid
    (dl (Libnames.qualid_of_string "Containers.OrderedType.compare"))
let mk_cmp x y =
  CAst.make @@ CApp ((None, mkRefC compare_ref),
	[mkIdentC x, None; mkIdentC y, None])

let pathole = CAst.make @@ CPatAtom (None)
let rec lholes = function
  | 0 -> []
  | n -> pathole::(lholes (n-1))
let patc r l = CAst.make @@ CPatCstr (r, None, l)
let rec lpats v acc = function
  | 0 -> acc
  | n ->
      let p = CAst.make @@ CPatAtom (Some (Libnames.Ident
					     (dl (Nameops.make_ident v (Some n))))) in
      lpats v (p::acc) (n-1)

let rec lvars acc base n =
  match n with
    | 0 -> acc
    | n ->
	let xn = Nameops.make_ident base (Some n) in
	  lvars (xn::acc) base (n-1)

let lexi_eqn_constr r carity =
  let rec branch xs ys =
    match xs, ys with
      | [], [] -> mkIdentC id_Eq
      | [x], [y] -> mk_cmp x y
      | x::xs, y::ys ->
	  let item = [mk_cmp x y, None, None] in
	  let brlt =
	    (None,
	     ([(Loc.tag [patc ref_Lt []])], mkIdentC id_Lt)) in
	  let breq =
	    (None,
	     ([(Loc.tag [patc ref_Eq []])], branch xs ys)) in
	  let brgt =
	    (None,
	     ([(Loc.tag [patc ref_Gt []])], mkIdentC id_Gt)) in
	  CAst.make @@ CCases (RegularStyle, None, item,
			       [brlt; breq; brgt])
      | _, _ -> failwith "Lists should have the same size"
  in
  let xbar = lvars [] "x" carity in
  let ybar = lvars [] "y" carity in
    (None,
     ([(Loc.tag [patc r (lpats "x" [] carity);
	patc r (lpats "y" [] carity)])],
     branch xbar ybar))

let rec branches_constr cmpid names arities =
  match names, arities with
    | [], [] -> []
    | [cid], [carity] ->
	let r = Libnames.Ident (dl cid) in
	let eqn_lexi = lexi_eqn_constr r carity in
	  [eqn_lexi]
    | cid::otherids, carity::otherars ->
	let r = Libnames.Ident (dl cid) in
	let eqn_lexi = lexi_eqn_constr r carity in
	let eqn_inter1 =
	  (None, ([(Loc.tag [patc r (lholes carity); pathole])], mkIdentC id_Lt)) in
	let eqn_inter2 =
	  (None, ([(Loc.tag [pathole; patc r (lholes carity)])], mkIdentC id_Gt)) in
	  eqn_lexi::eqn_inter1::eqn_inter2::
	    (branches_constr cmpid otherids otherars)
    | _, _ -> failwith "Lists should have the same lengths."

let make_cmp_def ind mind body =
  let id_t = body.Declarations.mind_typename in
  let id_cmp = add_suffix id_t "_cmp" in
  let names = Array.to_list body.Declarations.mind_consnames in
  let decls = Array.to_list body.Declarations.mind_consnrealdecls in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let items = [mkIdentC x, None, None;
	       mkIdentC y, None, None] in
  let branches = branches_constr id_cmp names decls in
  let body = CAst.make @@ CCases (RegularStyle, None, items, branches) in
  let def =
    CLambdaN ([([dl (Names.Name x); dl (Names.Name y)],
		Default Decl_kinds.Explicit,
		mkIdentC id_t)],
	      body) in
    id_cmp, CAst.make @@ def

(* proving that the equality is an [Equivalence] *)
let load_tactic s =
  Tacinterp.interp
    (Tacexpr.TacArg
       (None, Tacexpr.Reference
	  (Libnames.Ident (dl (Names.Id.of_string s)))))

let load_tactic_args s lids =
  let args =
    List.map (fun id -> Tacexpr.Reference (Libnames.Ident (dl id))) lids
  in
  Tacinterp.interp
    (Tacexpr.TacArg
       (Loc.tag @@ Tacexpr.TacCall ( Loc.tag
				       (Libnames.Ident (dl (Names.Id.of_string s)),
					args))))

open Tacticals

let property_kind = (Decl_kinds.Global, false, Decl_kinds.Proof Decl_kinds.Property)
let lemma_kind = (Decl_kinds.Global, false, Decl_kinds.Proof Decl_kinds.Lemma)

let dummy_hook = Lemmas.mk_hook (fun _ _ -> ())

let get_context ty =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, _ty = Typing.type_of env sigma ty in
   sigma

let prove_refl indconstr mind body =
  let id_t = body.Declarations.mind_typename in
  let id_eq = add_suffix id_t "_eq" in
  let x = Nameops.make_ident "x" None in
  let ceq = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_eq)))) in
  let goal =
    mkNamedProd x indconstr
		(mkApp (ceq, [| mkVar x; mkVar x |])) in
  let refltactic =
    load_tactic "rinductive_refl"
  in
    Lemmas.start_proof (add_suffix id_t "_eq_refl")
      property_kind (get_context goal) goal dummy_hook;
    ignore(Pfedit.by refltactic);
    Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None))

let prove_sym indconstr mind body =
  let id_t = body.Declarations.mind_typename in
  let id_eq = add_suffix id_t "_eq" in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let ceq = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_eq)))) in
  let goal =
    mkNamedProd x indconstr
      (mkNamedProd y indconstr
	 (mkArrow
	    (mkApp (ceq, [| mkVar x; mkVar y |]))
	    (mkApp (ceq, [| mkVar y; mkVar x |])))) in
  let symtactic =
    load_tactic "rinductive_sym"
  in
    Lemmas.start_proof (add_suffix id_t "_eq_sym")
      property_kind (get_context goal) goal dummy_hook;
    ignore(Pfedit.by symtactic);
    Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None))

let prove_trans indconstr mind body =
  let id_t = body.Declarations.mind_typename in
  let id_eq = add_suffix id_t "_eq" in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let z = Nameops.make_ident "z" None in
  let ceq = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_eq)))) in
  let goal =
    mkNamedProd x indconstr
      (mkNamedProd y indconstr
	 (mkNamedProd z indconstr
	    (mkArrow
	       (mkApp (ceq, [| mkVar x; mkVar y |]))
	       (mkArrow
		  (mkApp (ceq, [| mkVar y; mkVar z |]))
		  (mkApp (ceq, [| mkVar x; mkVar z |]))
	       )))) in
  let transtactic =
    load_tactic "rinductive_trans"
  in
    Lemmas.start_proof (add_suffix id_t "_eq_trans")
      property_kind (get_context goal) goal dummy_hook;
    ignore(Pfedit.by transtactic);
    Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None))

let prove_Equivalence indconstr mind body =
  prove_refl indconstr mind body;
  prove_sym indconstr mind body;
  prove_trans indconstr mind body;
  let id_t = body.Declarations.mind_typename in
  let id_equiv = add_suffix id_t "_eq_Equivalence" in
  let equiv = CAst.make @@
    CApp ((None, mkIdentC (Names.Id.of_string "Build_Equivalence")),
	  [hole, None;
	   mkIdentC (add_suffix id_t "_eq_refl"), None;
	   mkIdentC (add_suffix id_t "_eq_sym"), None;
	   mkIdentC (add_suffix id_t "_eq_trans"), None])
  in
    declare_definition id_equiv
      (Decl_kinds.Global, false, Decl_kinds.Definition)
      None [] None equiv None dummy_hook (* ; *)
(*     Classes.declare_instance false (dl id_equiv) *)


(* proving that the ordering is a [StrictOrder] *)
let prove_lt_trans indconstr mind body =
  let id_t = body.Declarations.mind_typename in
  let id_lt = add_suffix id_t "_lt" in
  let id_eq = add_suffix id_t "_eq" in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let z = Nameops.make_ident "z" None in
  let clt = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_lt)))) in
  let ceq = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_eq)))) in
  let prove_eq_lt_and_gt () =
    let id_eq_sym = add_suffix id_t "_eq_sym" in
    let id_eq_trans = add_suffix id_t "_eq_trans" in
    let lemma_eq_lt =
      mkNamedProd x indconstr
	(mkNamedProd y indconstr
	   (mkNamedProd z indconstr
	      (mkArrow
		 (mkApp (ceq, [| mkVar x; mkVar y |]))
		 (mkArrow
		    (mkApp (clt, [| mkVar x; mkVar z |]))
		    (mkApp (clt, [| mkVar y; mkVar z |]))
		 )))) in
    let solve_eq_lt =
      load_tactic_args "rinductive_eq_lt" [id_eq_sym; id_eq_trans]
    in
    let lemma_eq_gt =
      mkNamedProd x indconstr
	(mkNamedProd y indconstr
	   (mkNamedProd z indconstr
	      (mkArrow
		 (mkApp (ceq, [| mkVar x; mkVar y |]))
		 (mkArrow
		    (mkApp (clt, [| mkVar z; mkVar x |]))
		    (mkApp (clt, [| mkVar z; mkVar y |]))
		 )))) in
    let solve_eq_gt =
      load_tactic_args "rinductive_eq_gt" [id_eq_trans]
    in
      Lemmas.start_proof (add_suffix id_t "_eq_lt")
	lemma_kind (get_context lemma_eq_lt) lemma_eq_lt dummy_hook;
      ignore(Pfedit.by solve_eq_lt);
      Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None));
      Lemmas.start_proof (add_suffix id_t "_eq_gt")
	lemma_kind (get_context lemma_eq_gt) lemma_eq_gt dummy_hook;
      ignore(Pfedit.by solve_eq_gt);
      Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None))
  in
  let goal =
    mkNamedProd x indconstr
      (mkNamedProd y indconstr
	 (mkNamedProd z indconstr
	    (mkArrow
	       (mkApp (clt, [| mkVar x; mkVar y |]))
	       (mkArrow
		  (mkApp (clt, [| mkVar y; mkVar z |]))
		  (mkApp (clt, [| mkVar x; mkVar z |]))
	       )))) in
  let transtactic =
    load_tactic_args "rinductive_lexico_trans"
      [add_suffix id_t "_eq_sym"; add_suffix id_t "_eq_trans";
       add_suffix id_t "_eq_gt"; add_suffix id_t "_eq_lt"]
  in
  prove_eq_lt_and_gt ();
  Lemmas.start_proof (add_suffix id_t "_lt_trans")
    property_kind (get_context goal) goal dummy_hook;
  ignore(Pfedit.by transtactic);
  Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None))

let prove_lt_irrefl indconstr mind body =
  let id_t = body.Declarations.mind_typename in
  let id_lt = add_suffix id_t "_lt" in
  let id_eq = add_suffix id_t "_eq" in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let clt = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_lt)))) in
  let ceq = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_eq)))) in
  let cfalse = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl (Names.Id.of_string "False"))))) in
  let goal =
    mkNamedProd x indconstr
      (mkNamedProd y indconstr
	 (mkArrow
	    (mkApp (clt, [| mkVar x; mkVar y |]))
	    (mkArrow
	       (mkApp (ceq, [| mkVar x; mkVar y |]))
	       (mkApp (cfalse, [| |]))
	    ))) in
  let irrefltactic =
    load_tactic "rinductive_irrefl"
  in
    Lemmas.start_proof (add_suffix id_t "_lt_irrefl")
      property_kind (get_context goal) goal dummy_hook;
    ignore(Pfedit.by irrefltactic);
    Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None))

let build_strictorder_ref =
  Libnames.Qualid
    (dl (Libnames.qualid_of_string "Containers.OrderedType.Build_StrictOrder"))
let prove_StrictOrder indconstr mind body =
  prove_lt_trans indconstr mind body;
  prove_lt_irrefl indconstr mind body;
  let id_t = body.Declarations.mind_typename in
  let id_strict = add_suffix id_t "_lt_StrictOrder" in
  let strict = CAst.make @@
    CApp ((None, mkRefC build_strictorder_ref),
	  [hole, None; hole, None; hole, None;
	   mkIdentC (add_suffix id_t "_eq_Equivalence"), None;
	   mkIdentC (add_suffix id_t "_lt_trans"), None;
	   mkIdentC (add_suffix id_t "_lt_irrefl"), None])
  in
    declare_definition id_strict
      (Decl_kinds.Global, false, Decl_kinds.Definition)
      None [] None strict None dummy_hook


(* proving the [OrderedType] instance *)
let prove_t_compare_spec indconstr mind body =
  let id_t = body.Declarations.mind_typename in
  let id_eq = add_suffix id_t "_eq" in
  let id_lt = add_suffix id_t "_lt" in
  let id_cmp = add_suffix id_t "_cmp" in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let clt = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_lt)))) in
  let ceq = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_eq)))) in
  let ccmp = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id_cmp)))) in
  let ccomp_spec = EConstr.of_constr (Universes.constr_of_global
    (Nametab.global (Libnames.Ident
		       (dl (Names.Id.of_string "compare_spec"))))) in
  let goal =
    mkNamedProd x indconstr
      (mkNamedProd y indconstr
	 (mkApp (ccomp_spec,
		 [| indconstr; ceq; clt; mkVar x; mkVar y;
		    mkApp (ccmp, [| mkVar x; mkVar y |]) |]))) in
  let spectactic =
    load_tactic_args "rsolve_compare_spec" [add_suffix id_t "_eq_sym"]
  in
  Lemmas.start_proof (add_suffix id_t "_compare_spec")
    property_kind (get_context goal) goal dummy_hook;
  ignore(Pfedit.by spectactic);
  Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None))

let build_ot_ref =
  Libnames.Qualid
    (dl (Libnames.qualid_of_string "Containers.OrderedType.Build_OrderedType"))
let prove_OrderedType indconstr mind body =
  prove_t_compare_spec indconstr mind body;
  let id_t = body.Declarations.mind_typename in
  let id_ot = add_suffix id_t "_OrderedType" in
  let tc = Typeclasses.class_info
	     (Coqlib.find_reference "containersplugin"
				    ["Containers";"OrderedType"] "OrderedType") in
  let ot = CAst.make @@
    CApp ((None, mkRefC build_ot_ref),
	  [hole, None; hole, None; hole, None;
	   mkIdentC (add_suffix id_t "_eq_Equivalence"), None;
	   mkIdentC (add_suffix id_t "_lt_StrictOrder"), None;
	   hole, None;
	   mkIdentC (add_suffix id_t "_compare_spec"), None])
  in
    declare_definition id_ot
      (Decl_kinds.Global, false, Decl_kinds.Definition)
      None [] None ot None
      (Lemmas.mk_hook (fun loc gr ->
		       API.Typeclasses.add_instance
			 (API.Typeclasses.new_instance tc Hints.empty_hint_info
						       (loc=Decl_kinds.Local) false gr)))

let generate_simple_ot gref =
  let gindref = Nametab.global gref in
  let indconstr = Universes.constr_of_global gindref in
  let indeconstr = EConstr.of_constr indconstr in
  (* retrieve the inductive type *)
  let (ind, ctx) =
    Inductive.find_inductive (Global.env ()) indconstr in
  let (mind, ibody) = Global.lookup_inductive (fst ind) in
  fprintf std_formatter "%a" print_ind_body ibody;
  (* define the equality predicate *)
  let mutual_eq = make_eq_mutual ind mind ibody in
  (* fprintf std_formatter "%a" print_inductive_def mutual_eq; *)
  Command.do_mutual_inductive mutual_eq false false false Decl_kinds.Finite;
  (* define the strict ordering predicate *)
  let mutual_lt = make_lt_mutual ind mind ibody in
  (* fprintf std_formatter "%a" print_inductive_def mutual_lt; *)
  Command.do_mutual_inductive mutual_lt false false false Decl_kinds.Finite;
  (* declare the comparison function *)
  let id_cmp, ttt = make_cmp_def ind mind ibody in
    declare_definition id_cmp
      (Decl_kinds.Global, false, Decl_kinds.Definition)
      None [] None ttt None dummy_hook;
  (* prove the Equivalence instance *)
  prove_Equivalence indeconstr mind ibody;
  (* prove the StrictOrder instance *)
  prove_StrictOrder indeconstr mind ibody;
  (* prove the OrderedType instance *)
  prove_OrderedType indeconstr mind ibody

(* for recursive datatypes *)

open Declarations
open Declareops

let print_ind (mind,index) =
  Printf.sprintf "(%s, %d)" (Names.string_of_mind mind) index

let print_recarg = function
  | Norec -> qs "Norec"
  | Mrec ind -> qs (Printf.sprintf "Mrec %s" (print_ind ind))
  | Imbr ind -> qs (Printf.sprintf "Inductive %s" (print_ind ind))

let rec map3 f l1 l2 l3 =
  match l1, l2, l3 with
    | [], [], [] -> []
    | a::q, b::r, c::s -> (f a b c)::(map3 f q r s)
    | _, _, _ ->
	failwith "Invalid_argument [map3] : lists should have the same length"

let req_constr_i eqid cid wp carity cmask =
  let xbar = app_expl_i [] "x" carity in
  let ybar = app_expl_i [] "y" carity in
  let cx = CAst.make @@ CApp ((None, mkIdentC cid), xbar) in
  let cy = CAst.make @@ CApp ((None, mkIdentC cid), ybar) in
  let rec eq_n_i acc cmask n =
    match n, cmask with
      | 0, [] -> acc
      | n, mask::cmask ->
	  let xn = Nameops.make_ident "x" (Some n) in
	  let yn = Nameops.make_ident "y" (Some n) in
	  let t =
	    if mask then
	      CApp ((None, mkIdentC eqid),
		    [mkIdentC xn, None; mkIdentC yn, None])
	    else
	      mk_equiv xn yn
	  in
	    eq_n_i
	      (([None,Names.Anonymous],Default Decl_kinds.Explicit, CAst.make @@ t) :: acc)
	      cmask
	      (n-1)
      | _, _ -> failwith "Mask does not match arity."
  in
  CAst.make @@ CProdN ((prod_n_i [] carity) @
			 (eq_n_i [] (List.rev cmask) carity),
		       CAst.make @@ CApp ((None, mkIdentC eqid),
					  [cx, None; cy, None]))

let rmake_eq_mutual ind mask mind body =
  let id_t = body.mind_typename in
  let id_eq = add_suffix id_t "_eq" in
  let wp = body.mind_recargs in
  let lconstr =
    map3 (fun cid carity cmask ->
	    (cf (dl (add_suffix id_eq ("_"^(Names.Id.to_string cid))),
		 req_constr_i id_eq cid wp carity cmask)))
      (Array.to_list body.mind_consnames)
      (Array.to_list body.mind_consnrealdecls)
      mask
  in
    [((Loc.tag @@ id_eq, None), [], Some (bin_rel_t id_t) , lconstr), []]

let rlexi_constr eqid ltid cid carity cmask =
  let xbar = app_expl_i [] "x" carity in
  let ybar = app_expl_i [] "y" carity in
  let cx = CAst.make @@ CApp ((None, mkIdentC cid), xbar) in
  let cy = CAst.make @@ CApp ((None, mkIdentC cid), ybar) in
  let rec one_lexico_case acc n mask = match n, mask with
    | 0, [] -> acc
    | n, mask::masks ->
	let xn = Nameops.make_ident "x" (Some n) in
	let yn = Nameops.make_ident "y" (Some n) in
	let t =
	  if mask then
	    CApp ((None, mkIdentC eqid),
		  [mkIdentC xn, None; mkIdentC yn, None])
	  else mk_equiv xn yn in
	one_lexico_case
	  (([None,Names.Anonymous],Default Decl_kinds.Explicit, CAst.make @@ t) :: acc)
	  (n-1) masks
    | _, _ -> failwith "Mask does not match arity."
  in
  let rec all_lexico_cases goal acc n cmask = match n, cmask with
    | 0, [] -> acc
    | n, mask::masks ->
	let xn = Nameops.make_ident "x" (Some n) in
	let yn = Nameops.make_ident "y" (Some n) in
	let t =
	  if mask then
	    CApp ((None, mkIdentC ltid),
		  [mkIdentC xn, None; mkIdentC yn, None])
	  else mk_lt xn yn in
	let c = CAst.make @@
		  CProdN (one_lexico_case [[None,Names.Anonymous],Default Decl_kinds.Explicit, CAst.make @@ t]
					  (n-1) masks, goal) in
	let name = add_suffix ltid ("_"^(Names.Id.to_string cid)^
				      "_"^(string_of_int n)) in
	  all_lexico_cases goal ((name, c)::acc) (n-1) masks
    | _, _ -> failwith "Mask does not match arity."
  in
  let goal =
    CAst.make @@ CApp ((None, mkIdentC ltid), [cx, None; cy, None]) in
  let cases =
    all_lexico_cases goal [] carity (List.rev cmask) in
    List.map (fun (name, c) ->
		cf (dl name,
		    CAst.make @@ CProdN ((prod_n_i [] carity), c)))
      cases

let rec rlt_constr eqid ltid names arities mask =
  match names, arities, mask with
    | [], [], [] -> []
    | cid::otherids, carity::otherars, cmask::othermasks ->
	let lexi = rlexi_constr eqid ltid cid carity cmask in
	let inter = inter_constr ltid cid carity otherids otherars in
	  lexi@inter@(rlt_constr eqid ltid otherids otherars othermasks)
    | _, _, _ -> failwith "Lists should have the same lengths."

let rmake_lt_mutual ind mask mind body =
  let id_t = body.Declarations.mind_typename in
  let id_lt = add_suffix id_t "_lt" in
  let id_eq = add_suffix id_t "_eq" in
  let names = Array.to_list body.Declarations.mind_consnames in
  let decls = Array.to_list body.Declarations.mind_consnrealdecls in
  let lconstr = rlt_constr id_eq id_lt names decls mask in
    [((dl id_lt, None), [], Some (bin_rel_t id_t) , lconstr), []]

let mk_cmp_if cmpid x y mask =
  if mask then
    CAst.make @@ CApp ((None, mkIdentC cmpid),
	  [mkIdentC x, None; mkIdentC y, None])
  else mk_cmp x y

let rlexi_eqn_constr r cmpid carity cmask =
  let rec branch xs ys cmask =
    match xs, ys, cmask with
      | [], [], [] -> mkIdentC id_Eq
      | [x], [y], [mask] -> mk_cmp_if cmpid x y mask
      | x::xs, y::ys, mask::masks ->
	 let item = [mk_cmp_if cmpid x y mask, None, None] in
	 let brlt =
	   (None,
	    ([(Loc.tag [patc ref_Lt []])], mkIdentC id_Lt)) in
	 let breq =
	   (None,
	    ([(Loc.tag [patc ref_Eq []])], branch xs ys masks)) in
	 let brgt =
	   (None,
	    ([(Loc.tag [patc ref_Gt []])], mkIdentC id_Gt)) in
	 CAst.make @@ CCases (RegularStyle, None, item,
			      [brlt; breq; brgt])
      | _, _, _ -> failwith "Lists should have the same size"
  in
  let xbar = lvars [] "x" carity in
  let ybar = lvars [] "y" carity in
    (None,
     ([(Loc.tag @@ [patc r (lpats "x" [] carity);
			patc r (lpats "y" [] carity)])],
     branch xbar ybar cmask))

let rec rbranches_constr cmpid names arities mask =
  match names, arities, mask with
    | [], [], [] -> []
    | [cid], [carity], [cmask] ->
	let r = Libnames.Ident (dl cid) in
	let eqn_lexi = rlexi_eqn_constr r cmpid carity cmask in
	  [eqn_lexi]
    | cid::otherids, carity::otherars, cmask::othermasks ->
	let r = Libnames.Ident (dl cid) in
	let eqn_lexi = rlexi_eqn_constr r cmpid carity cmask in
	let eqn_inter1 =
	  (None,
	   ([(Loc.tag [patc r (lholes carity); pathole])],
	   mkIdentC id_Lt)) in
	let eqn_inter2 =
	  (None,
	   ([(Loc.tag [pathole; patc r (lholes carity)])],
	   mkIdentC id_Gt)) in
	  eqn_lexi::eqn_inter1::eqn_inter2::
	    (rbranches_constr cmpid otherids otherars othermasks)
    | _, _, _ -> failwith "Lists should have the same lengths."

let rmake_cmp_def ind mask mind body =
  let id_t = body.Declarations.mind_typename in
  let id_cmp = add_suffix id_t "_cmp" in
  let names = Array.to_list body.Declarations.mind_consnames in
  let decls = Array.to_list body.Declarations.mind_consnrealdecls in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let items = [mkIdentC x, None, None;
	       mkIdentC y, None, None] in
  let branches = rbranches_constr id_cmp names decls mask in
  let body =  CAst.make @@ CCases (RegularStyle, None, items, branches) in
    ((dl id_cmp, None), (None, Constrexpr.CStructRec),
     [CLocalAssum([dl (Names.Name x); dl (Names.Name y)],
		    Default Decl_kinds.Explicit, mkIdentC id_t)],
     ccomparison,
     Some body)



let dest_subterms p =
  let (ra,cstrs) = Rtree.dest_node p in
  assert (match ra with Norec -> false | _ -> true);
  Array.map (fun t -> Array.to_list (snd (Rtree.dest_node t))) cstrs

let make_mask body =
  let wp = body.mind_recargs in
  let f p = Rtree.equal (=) p wp in
    List.map (List.map f) (Array.to_list (dest_subterms wp))

let generate_rec_ot gref =
  let gindref = Nametab.global gref in
  let indconstr = Universes.constr_of_global gindref in
  let indeconstr = EConstr.of_constr indconstr in
  (* retrieve the inductive type *)
  let env = Global.env () in
  let evd = Evd.from_env env in
  let ind =
    Inductiveops.find_rectype env evd (EConstr.of_constr indconstr) in
  let (mind, ibody) = Global.lookup_inductive (Globnames.destIndRef gindref) in
    fprintf std_formatter "%a" print_ind_body ibody;
  let pptree = Rtree.pp_tree print_recarg ibody.Declarations.mind_recargs in
    if_verbose Feedback.msg_notice pptree;
  let mask = make_mask ibody in
    List.iter
      (fun paths ->
	 List.iter (fun b ->
		      fprintf std_formatter "%s "
			(if b then "rec " else "nonrec ")
		   ) paths;
	 fprintf std_formatter "\n"
      ) mask;
  (* define the equality predicate *)
  let mutual_eq = rmake_eq_mutual ind mask mind ibody in
  (*     fprintf std_formatter "%a" print_inductive_def mutual_eq; *)
  Command.do_mutual_inductive mutual_eq false false false Decl_kinds.Finite;
  (* define the strict ordering predicate *)
  let mutual_lt = rmake_lt_mutual ind mask mind ibody in
  (*     fprintf std_formatter "%a" print_inductive_def mutual_lt; *)
  Command.do_mutual_inductive mutual_lt false false false Decl_kinds.Finite;
  (* declare the comparison function *)
  let fexpr = rmake_cmp_def ind mask mind ibody in
  Command.do_fixpoint Decl_kinds.Global false [(fexpr, [])];
  (* prove the Equivalence instance *)
  prove_Equivalence indeconstr mind ibody;
  (* prove the StrictOrder instance *)
  prove_StrictOrder indeconstr mind ibody;
  (* prove the OrderedType instance *)
  prove_OrderedType indeconstr mind ibody

open Declarations

let c_of_id id =
  Universes.constr_of_global
    (Nametab.global (Libnames.Ident (dl id)))

exception FoundEqual of int
let make_masks mind =
  let roots = Array.map (fun b -> b.mind_recargs) mind.mind_packets in
  let f p =
    try
      Array.iteri (fun i wp ->
		     if Rtree.eq_rtree (=) p wp then raise (FoundEqual i))
	roots;
      (-1)
    with FoundEqual i -> i
  in
  Array.map (fun wp ->
	       List.map (List.map f) (Array.to_list (dest_subterms wp)))
    roots

let meq_constr_i eqid eqids cid carity (cmask : int list) =
  let xbar = app_expl_i [] "x" carity in
  let ybar = app_expl_i [] "y" carity in
  let cx = CAst.make @@ CApp ((None, mkIdentC cid), xbar) in
  let cy = CAst.make @@ CApp ((None, mkIdentC cid), ybar) in
  let rec eq_n_i acc cmask n =
    match n, cmask with
      | 0, [] -> acc
      | n, mask::cmask ->
	  let xn = Nameops.make_ident "x" (Some n) in
	  let yn = Nameops.make_ident "y" (Some n) in
	  let t =
	    if mask >= 0 then
	      CApp ((None, mkIdentC eqids.(mask)),
		    [mkIdentC xn, None; mkIdentC yn, None])
	    else
	      mk_equiv xn yn
	  in
	    eq_n_i
	      (([dl Names.Anonymous],Default Decl_kinds.Explicit, CAst.make @@ t) :: acc)
	      cmask
	      (n-1)
      | _, _ -> failwith "Mask does not match arity."
  in
  CAst.make @@ CProdN ((prod_n_i [] carity) @
			 (eq_n_i [] (List.rev cmask) carity),
		       CAst.make @@ (CApp ((None, mkIdentC eqid),
					   [cx, None; cy, None])))

let mmake_eq_mutual ind (masks : int list list array) mind =
  let ids = Array.map (fun b -> b.mind_typename) mind.mind_packets in
  let ids_eq = Array.map (fun id -> add_suffix id "_eq") ids in
  let lconstrs =
    Array.mapi
      (fun i body ->
	 let id_eq = ids_eq.(i) in
	 let mask = masks.(i) in
	   map3 (fun cid carity cmask ->
		   (cf (dl (add_suffix id_eq
			      ("_"^(Names.Id.to_string cid))),
			meq_constr_i id_eq ids_eq cid carity cmask)))
	     (Array.to_list body.mind_consnames)
	     (Array.to_list body.mind_consnrealdecls)
	     mask)
      mind.mind_packets
  in
    Array.to_list
      (Array.mapi (fun i lconstr ->
		     ((dl ids_eq.(i), None), [], Some (bin_rel_t ids.(i)), lconstr),
		     [])
	 lconstrs)

let do_proofs goals tac =
  let env = Global.env () in
  let evd = ref (Evd.from_env env) in
  let do_proof (name,goal) =
    let egoal = Constrintern.interp_constr_evars env evd (CAst.make goal) in
    Lemmas.start_proof name property_kind !evd egoal dummy_hook;
    ignore(Pfedit.by tac);
    Lemmas.save_proof (Vernacexpr.Proved(Vernacexpr.Transparent,None)) in
  ignore(List.map do_proof goals)



let mprove_refl k ids ids_eq mind =
  let x = Nameops.make_ident "x" None in
  let ceq i = mkIdentC ids_eq.(i) in
  let goal i =
    (CProdN ([[dl (Names.Name x)],
	      Default Decl_kinds.Explicit,
	      mkIdentC ids.(i)],
	     mkAppC (ceq i, [mkIdentC x; mkIdentC x]))) in
  let goals =
    Array.to_list (Array.mapi
		     (fun i id_eq -> (add_suffix id_eq "_refl", goal i))
		     ids_eq) in
  let refltactic =
    load_tactic (match k with
		   | Simple -> "inductive_refl"
		   | Recursive -> "rinductive_refl"
		   | Mutual -> "minductive_refl")
  in
  do_proofs goals refltactic



let mprove_sym k ids ids_eq mind =
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let ceq i = mkIdentC ids_eq.(i) in
  let goal i =
    CProdN ([[dl (Names.Name x); dl (Names.Name y)],
	     Default Decl_kinds.Explicit,
	     mkIdentC ids.(i);
	     [None, Names.Anonymous],
	     Default Decl_kinds.Explicit,
	     mkAppC (ceq i, [mkIdentC x; mkIdentC y])],
	    mkAppC (ceq i, [mkIdentC y; mkIdentC x])) in
  let goals =
    Array.to_list (Array.mapi
		     (fun i id_eq ->
			(add_suffix id_eq "_sym", goal i)) ids_eq) in
  let symtactic =
    load_tactic (match k with
		   | Simple -> "inductive_sym"
		   | Recursive -> "rinductive_sym"
		   | Mutual -> "minductive_sym")
  in
  do_proofs goals symtactic


let mprove_trans k ids ids_eq mind =
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let z = Nameops.make_ident "z" None in
  let ceq i = mkIdentC ids_eq.(i) in
  let goal i =
    CProdN ([[dl (Names.Name x); dl (Names.Name y); dl (Names.Name z)],
	     Default Decl_kinds.Explicit,
	     mkIdentC ids.(i);
	     [None, Names.Anonymous],
	     Default Decl_kinds.Explicit,
	     mkAppC (ceq i, [mkIdentC x; mkIdentC y]);
	     [None, Names.Anonymous],
	     Default Decl_kinds.Explicit,
	     mkAppC (ceq i, [mkIdentC y; mkIdentC z])],
	    mkAppC (ceq i, [mkIdentC x; mkIdentC z])) in
  let goals =
    Array.to_list (Array.mapi
		     (fun i id_eq ->
			(add_suffix id_eq "_trans", goal i)) ids_eq) in
  let transtactic =
    load_tactic (match k with
		   | Simple -> "inductive_trans"
		   | Recursive -> "rinductive_trans"
		   | Mutual -> "minductive_trans")
  in
  do_proofs goals transtactic

let mkARefC id = None, Libnames.Ident (None, id), None

let mprove_Equivalence k mind =
  let ids = Array.map (fun body -> body.mind_typename) mind.mind_packets in
  let ids_eq = Array.map (fun id_t -> add_suffix id_t "_eq") ids in
  let ids_equiv = Array.map (fun id -> add_suffix id "_Equivalence") ids_eq in
    mprove_refl k ids ids_eq mind;
    mprove_sym k ids ids_eq mind;
    mprove_trans k ids ids_eq mind;
  let equiv i =
    CAst.make @@ CAppExpl ((mkARefC (Names.Id.of_string "Build_Equivalence")),
			   [hole; hole;
			    mkIdentC (add_suffix ids.(i) "_eq_refl");
			    mkIdentC (add_suffix ids.(i) "_eq_sym");
			    mkIdentC (add_suffix ids.(i) "_eq_trans")])
  in
    Array.iteri (fun i id_equiv ->
		   declare_definition id_equiv
		     (Decl_kinds.Global, false, Decl_kinds.Definition)
		     None [] None (equiv i) None dummy_hook)
      ids_equiv

let mlexi_constr ids_eq ids_lt ltid cid carity cmask =
  let xbar = app_expl_i [] "x" carity in
  let ybar = app_expl_i [] "y" carity in
  let cx = CAst.make @@ CApp ((None, mkIdentC cid), xbar) in
  let cy = CAst.make @@ CApp ((None, mkIdentC cid), ybar) in
  let rec one_lexico_case acc n mask = match n, mask with
    | 0, [] -> acc
    | n, mask::masks ->
	let xn = Nameops.make_ident "x" (Some n) in
	let yn = Nameops.make_ident "y" (Some n) in
	let t =
	  if mask >= 0 then
	    CApp ((None, mkIdentC ids_eq.(mask)),
		  [mkIdentC xn, None; mkIdentC yn, None])
	  else mk_equiv xn yn in
	one_lexico_case
	  (([None,Names.Anonymous],Default Decl_kinds.Explicit, CAst.make @@ t) :: acc)
	  (n-1) masks
    | _, _ -> failwith "Mask does not match arity."
  in
  let rec all_lexico_cases goal acc n cmask = match n, cmask with
    | 0, [] -> acc
    | n, mask::masks ->
	let xn = Nameops.make_ident "x" (Some n) in
	let yn = Nameops.make_ident "y" (Some n) in
	let t =
	  if mask >= 0 then
	    CApp ((None, mkIdentC ids_lt.(mask)),
		  [mkIdentC xn, None; mkIdentC yn, None])
	  else mk_lt xn yn in
	let c = CAst.make @@ CProdN (one_lexico_case [[dl Names.Anonymous],Default Decl_kinds.Explicit, CAst.make @@ t] (n-1) masks,
			goal) in
	let name = add_suffix ltid ("_"^(Names.Id.to_string cid)^
				      "_"^(string_of_int n)) in
	  all_lexico_cases goal ((name, c)::acc) (n-1) masks
    | _, _ -> failwith "Mask does not match arity."
  in
  let goal =
    CAst.make @@ CApp ((None, mkIdentC ltid), [cx, None; cy, None]) in
  let cases =
    all_lexico_cases goal [] carity (List.rev cmask) in
    List.map (fun (name, c) ->
		cf (dl name,
		    CAst.make @@ CProdN ((prod_n_i [] carity), c)))
      cases

let rec mlt_constr ids_eq ids_lt ltid names arities mask =
  match names, arities, mask with
    | [], [], [] -> []
    | cid::otherids, carity::otherars, cmask::othermasks ->
	let lexi = mlexi_constr ids_eq ids_lt ltid cid carity cmask in
	let inter = inter_constr ltid cid carity otherids otherars in
	  lexi@inter@(mlt_constr ids_eq ids_lt ltid
			otherids otherars othermasks)
    | _, _, _ -> failwith "Lists should have the same lengths."

let mmake_lt_mutual ind masks mind =
  let ids = Array.map (fun body -> body.mind_typename) mind.mind_packets in
  let ids_lt = Array.map (fun id_t -> add_suffix id_t "_lt") ids in
  let ids_eq = Array.map (fun id_t -> add_suffix id_t "_eq") ids in
  let lconstrs =
    Array.mapi (fun i body ->
		  let names = Array.to_list body.mind_consnames in
		  let decls = Array.to_list body.mind_consnrealdecls in
		  mlt_constr ids_eq ids_lt ids_lt.(i) names decls masks.(i))
      mind.mind_packets
  in
  Array.to_list
    (Array.mapi (fun i lconstr ->
		   ((dl ids_lt.(i), None), [], Some (bin_rel_t ids.(i)), lconstr),
		   [])
       lconstrs)

(* proving that the ordering is a [StrictOrder] *)
open Tacexpr
open Genarg
open Stdarg

let apply_tactic s tacs =
  Tacexpr.TacArg
    (Loc.tag @@ Tacexpr.TacCall (Loc.tag
				   (Libnames.Ident (dl (Names.Id.of_string s)),
				    List.map (fun t -> Tacexpr.Tacexp t) tacs)))

let seq_eapply lids : raw_tactic_expr =
  let b = Nameops.make_ident "__B" None in
  let apply id =
    TacAtom (Loc.tag @@
	     TacApply (true, false,
		       [(None, (mkIdentC id,
			 Misctypes.ImplicitBindings [mkIdentC b]))],
		       None))
  in
    TacFun ([Names.Name b], TacFirst (List.map apply lids))

let seq_eapply_sym lids lsyms : raw_tactic_expr =
  let b = Nameops.make_ident "__B" None in
  let apply_with_sym id idsym =
    TacThens(
      TacAtom (Loc.tag @@
	       TacApply (true, false,
			 [(None, (mkIdentC id,
			   Misctypes.ImplicitBindings [mkIdentC b]))],
			 None)),
      [
	TacAtom (Loc.tag @@
		 TacApply (true, false,
			   [(None, (mkIdentC idsym, Misctypes.NoBindings))],
			   None));
	TacId []
      ])
  in
    TacFun ([Names.Name b], TacFirst (List.map2 apply_with_sym lids lsyms))


let mprove_lt_trans k ids ids_eq ids_lt mind =
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let z = Nameops.make_ident "z" None in
  let clt i = mkIdentC ids_lt.(i) in
  let ceq i = mkIdentC ids_eq.(i) in
  let eauto = {
    mltac_name = {
      mltac_plugin = "ltac_plugin";
      mltac_tactic = "eauto";
    };
    mltac_index = 0 }
     in
(*  let eauto = {
    mltac_name = eauto;
    mltac_index = 0;
    (** Fragile, should change if eauto has more entries *)
  } in *)
  let solve_arg : raw_tactic_expr =
    let lems =
      Array.fold_left
	(fun acc id_eq ->
	   (mkIdentC (add_suffix id_eq "_sym"))::
	     (mkIdentC (add_suffix id_eq "_trans"))::acc
	) [] ids_eq in
	       TacML (Loc.tag @@ (eauto,
			  [TacGeneric (in_gen (rawwit (wit_opt Stdarg.wit_int_or_var)) None);
			   TacGeneric (in_gen (rawwit (wit_opt Stdarg.wit_int_or_var)) None);
			   TacGeneric (in_gen (rawwit G_auto.wit_auto_using) lems);
			   TacGeneric (in_gen (rawwit G_auto.wit_hintbases) (Some []))
			   ]))
  in
  let prove_eq_lt_and_gt () =
    let lemma_eq_lt i =
      CProdN ([[dl (Names.Name x); dl (Names.Name y); dl (Names.Name z)],
	       Default Decl_kinds.Explicit,
	       mkIdentC ids.(i);
	       [None,Names.Anonymous],
	       Default Decl_kinds.Explicit,
	       mkAppC (ceq i, [mkIdentC x; mkIdentC y]);
	       [None,Names.Anonymous],
	       Default Decl_kinds.Explicit,
	       mkAppC (clt i, [mkIdentC x; mkIdentC z])],
	      mkAppC (clt i, [mkIdentC y; mkIdentC z])) in
    let lemma_eq_gt i =
      CProdN ([[dl (Names.Name x); dl (Names.Name y); dl (Names.Name z)],
	       Default Decl_kinds.Explicit,
	       mkIdentC ids.(i);
	       [None,Names.Anonymous],
	       Default Decl_kinds.Explicit,
	       mkAppC (ceq i, [mkIdentC x; mkIdentC y]);
	       [None,Names.Anonymous],
	       Default Decl_kinds.Explicit,
	       mkAppC (clt i, [mkIdentC z; mkIdentC x])],
	      mkAppC (clt i, [mkIdentC z; mkIdentC y])) in
    let lemmas_eq_lt =
      Array.to_list (Array.mapi
		       (fun i id ->
			  (add_suffix id "_lt", lemma_eq_lt i)) ids_eq) in
    let eqlttactic =
      Tacinterp.interp (apply_tactic "minductive_eq_lt_gt"
			  [apply_tactic "msolve_eq_lt" [solve_arg]]) in
    let lemmas_eq_gt =
      Array.to_list (Array.mapi
		       (fun i id ->
			  (add_suffix id "_gt", lemma_eq_gt i)) ids_eq) in
    let eqgttactic =
      Tacinterp.interp (apply_tactic "minductive_eq_lt_gt"
			  [apply_tactic "msolve_eq_gt" [solve_arg]])
    in
    do_proofs lemmas_eq_lt eqlttactic;
    do_proofs lemmas_eq_gt eqgttactic
  in
  let goal i =
    CProdN ([[dl (Names.Name x); dl (Names.Name y); dl (Names.Name z)],
	     Default Decl_kinds.Explicit,
	     mkIdentC ids.(i);
	     [None,Names.Anonymous],
	     Default Decl_kinds.Explicit,
	     mkAppC (clt i, [mkIdentC x; mkIdentC y]);
	     [None,Names.Anonymous],
	     Default Decl_kinds.Explicit,
	     mkAppC (clt i, [mkIdentC y; mkIdentC z])],
	    mkAppC (clt i, [mkIdentC x; mkIdentC z])) in
  let goals =
    Array.to_list (Array.mapi
		     (fun i id_lt ->
		      (add_suffix id_lt "_trans", goal i)) ids_lt) in
  let transtactic =
    match k with
      | Simple -> load_tactic "inductive_lexico_trans"
      | Recursive ->
	  load_tactic_args "rinductive_lexico_trans"
	    [add_suffix ids_eq.(0) "_sym"; add_suffix ids_eq.(0) "_trans";
	     add_suffix ids_eq.(0) "_gt"; add_suffix ids_eq.(0) "_lt"]
      | _ ->
	  let leq = Array.to_list ids_eq in
	  let strans = seq_eapply
	    (List.map (fun id -> add_suffix id "_trans") leq) in
	  let seqgt = seq_eapply
	    (List.map (fun id -> add_suffix id "_gt") leq) in
	  let seqlt = seq_eapply_sym
	    (List.map (fun id -> add_suffix id "_lt") leq)
	    (List.map (fun id -> add_suffix id "_sym") leq) in
	  Tacinterp.interp (apply_tactic "minductive_lexico_trans"
			      [strans; seqgt; seqlt])
  in
  if k = Simple then ()
  else prove_eq_lt_and_gt ();
  do_proofs goals transtactic


let mprove_lt_irrefl k ids ids_eq ids_lt mind =
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let clt i = mkIdentC ids_lt.(i) in
  let ceq i = mkIdentC ids_eq.(i) in
  let cfalse = mkIdentC (Names.Id.of_string "False") in
  let goal i =
    CProdN ([[dl (Names.Name x); dl (Names.Name y)],
	     Default Decl_kinds.Explicit,
	     mkIdentC ids.(i);
	     [None,Names.Anonymous],
	     Default Decl_kinds.Explicit,
	     mkAppC (clt i, [mkIdentC x; mkIdentC y]);
	     [None,Names.Anonymous],
	     Default Decl_kinds.Explicit,
	     mkAppC (ceq i, [mkIdentC x; mkIdentC y])],
	    cfalse) in
  let goals =
    Array.to_list (Array.mapi
		     (fun i id ->
		      (add_suffix id "_irrefl",goal i)) ids_lt) in
  let irrefltactic =
    load_tactic (if k = Simple then "inductive_irrefl"
		 else "minductive_irrefl")
  in
  do_proofs goals irrefltactic

let mprove_StrictOrder k mind =
  let ids = Array.map (fun body -> body.mind_typename) mind.mind_packets in
  let ids_eq = Array.map (fun id_t -> add_suffix id_t "_eq") ids in
  let ids_lt = Array.map (fun id_t -> add_suffix id_t "_lt") ids in
  let ids_equiv = Array.map (fun id -> add_suffix id "_Equivalence") ids_eq in
  let ids_order = Array.map (fun id -> add_suffix id "_StrictOrder") ids_lt in
  mprove_lt_irrefl k ids ids_eq ids_lt mind;
  mprove_lt_trans k ids ids_eq ids_lt mind;
  let strict i =
    CAppExpl (
	  (None, build_strictorder_ref, None),
	  [hole; hole; hole;
	   mkIdentC ids_equiv.(i);
	   mkIdentC (add_suffix ids_lt.(i) "_trans");
	   mkIdentC (add_suffix ids_lt.(i) "_irrefl")])
  in
  Array.iteri (fun i id_order ->
		 declare_definition id_order
		   (Decl_kinds.Global, false, Decl_kinds.Definition)
		   None [] None (CAst.make (strict i)) None dummy_hook)
    ids_order

let mmk_cmp_if ids_cmp x y mask =
  if mask >= 0 then
    CAst.make @@ CApp ((None, mkIdentC ids_cmp.(mask)),
		       [mkIdentC x, None; mkIdentC y, None])
  else mk_cmp x y

let mlexi_eqn_constr r ids_cmp carity cmask =
  let rec branch xs ys cmask =
    match xs, ys, cmask with
      | [], [], [] -> mkIdentC id_Eq
      | [x], [y], [mask] -> mmk_cmp_if ids_cmp x y mask
      | x::xs, y::ys, mask::masks ->
	  let item = [mmk_cmp_if ids_cmp x y mask, None, None] in
	  let brlt =
	    (None,
	     ([(Loc.tag @@ [patc ref_Lt []])],
	      mkIdentC id_Lt)) in
	  let breq =
	    (None,
	     ([(Loc.tag @@ [patc ref_Eq []])],
	      branch xs ys masks)) in
	  let brgt =
	    (None,
	     ([(Loc.tag @@ [patc ref_Gt []])],
	      mkIdentC id_Gt)) in
	    CAst.make @@ CCases (RegularStyle, None, item,
				 [brlt; breq; brgt])
      | _, _, _ -> failwith "Lists should have the same size"
  in
  let xbar = lvars [] "x" carity in
  let ybar = lvars [] "y" carity in
    (None,
     ([(Loc.tag [patc r (lpats "x" [] carity);
		 patc r (lpats "y" [] carity)])],
      branch xbar ybar cmask))

let rec mbranches_constr ids_cmp names arities mask =
  match names, arities, mask with
    | [], [], [] -> []
    | [cid], [carity], [cmask] ->
	let r = Libnames.Ident (dl cid) in
	let eqn_lexi = mlexi_eqn_constr r ids_cmp carity cmask in
	  [eqn_lexi]
    | cid::otherids, carity::otherars, cmask::othermasks ->
	let r = Libnames.Ident (dl cid) in
	let eqn_lexi = mlexi_eqn_constr r ids_cmp carity cmask in
	let eqn_inter1 =
	  (None,
	   ([(Loc.tag [patc r (lholes carity); pathole])],
	   mkIdentC id_Lt)) in
	let eqn_inter2 =
	  (None,
	   ([(Loc.tag [pathole; patc r (lholes carity)])],
	   mkIdentC id_Gt)) in
	  eqn_lexi::eqn_inter1::eqn_inter2::
	    (mbranches_constr ids_cmp otherids otherars othermasks)
    | _, _, _ -> failwith "Lists should have the same lengths."

let mmake_cmp_def k ind masks mind =
  let ids = Array.map (fun body -> body.mind_typename) mind.mind_packets in
  let ids_cmp = Array.map (fun id_t -> add_suffix id_t "_cmp") ids in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let make_body i body =
    let names = Array.to_list body.Declarations.mind_consnames in
    let decls = Array.to_list body.Declarations.mind_consnrealdecls in
    let items = [mkIdentC x, None, None;
		 mkIdentC y, None, None] in
    let branches = mbranches_constr ids_cmp names decls masks.(i) in
    CAst.make @@ CCases (RegularStyle, None, items, branches)
  in
  let make_block i body =
    ((dl ids_cmp.(i), None), (None, Constrexpr.CStructRec),
     [CLocalAssum([dl (Names.Name x); dl (Names.Name y)],
		    Default Decl_kinds.Explicit, mkIdentC ids.(i))],
     ccomparison,
     Some (make_body i body))
  in
  match k with
    | Simple ->
	let def =
	  CLambdaN ([([dl (Names.Name x); dl (Names.Name y)],
		      Default Decl_kinds.Explicit,
		      mkIdentC ids.(0))],
		    make_body 0 mind.mind_packets.(0))
	in
	  declare_definition ids_cmp.(0)
	    (Decl_kinds.Global, false, Decl_kinds.Definition)
	    None [] None (CAst.make def) None dummy_hook
    | Recursive | Mutual ->
	let defs =
	  Array.to_list (Array.mapi
			   (fun i body -> make_block i body, [])
			   mind.mind_packets)
	in
	Command.do_fixpoint Decl_kinds.Global false defs

let using_sym_tac = ref (None:Tacexpr.ml_tactic_entry option)

let using_sym ?loc =
  let entry = match !using_sym_tac with
    | None ->
       let name = {
	 mltac_plugin = "containers_plugin";
	 mltac_tactic = "using_sym";
       } in
       let entry = {
	 mltac_name = name;
	 mltac_index = 0;
       } in
       let tac args _ =
	 let map v =
	   let id = Tacinterp.Value.cast (topwit Stdarg.wit_ident) v in
	   (fun ist sigma -> (sigma, (EConstr.of_constr (Universes.constr_of_global (Constrintern.global_reference id)))))
	 in
	 let args = List.map map args in
	 Auto.h_auto None args (Some [])
       in
       let _ = Tacenv.register_ml_tactic name [|tac|] in
       let _ = using_sym_tac := Some entry in
       entry
    | Some entry -> entry
  in
  fun ids ->
  let map id = TacGeneric (in_gen (rawwit Stdarg.wit_ident) id) in
  let ids = List.map map ids in
  TacML (Loc.tag (?loc:loc) (entry, ids))


(* proving the [OrderedType] instance *)
let mprove_compare_spec k ids mind =
  let ids_eq = Array.map (fun id_t -> add_suffix id_t "_eq") ids in
  let ids_lt = Array.map (fun id_t -> add_suffix id_t "_lt") ids in
  let ids_cmp = Array.map (fun id_t -> add_suffix id_t "_cmp") ids in
  let ids_sym = Array.map (fun id_t -> add_suffix id_t "_sym") ids_eq in
  let x = Nameops.make_ident "x" None in
  let y = Nameops.make_ident "y" None in
  let clt i = mkIdentC (ids_lt.(i)) in
  let ceq i = mkIdentC (ids_eq.(i)) in
  let ccmp i = mkIdentC (ids_cmp.(i)) in
  let ccomp_spec = mkIdentC (Names.Id.of_string "compare_spec") in
  let goal i =
    CProdN ([[dl (Names.Name x); dl (Names.Name y)],
	     Default Decl_kinds.Explicit,
	     mkIdentC ids.(i)],
	    mkAppC (ccomp_spec,
		    [ ceq i; clt i;
		      mkIdentC x; mkIdentC y;
		      (mkAppC (ccmp i, [ mkIdentC x; mkIdentC y ]))]))
  in
  let goals =
    Array.to_list (Array.mapi
		     (fun i id ->
			(add_suffix id "_compare_spec", goal i)) ids) in
  let using_sym = using_sym (Array.to_list ids_sym) in
  let comparespectactic = match k with
    | Simple -> load_tactic "solve_compare_spec"
    | Recursive ->
	load_tactic_args "rsolve_compare_spec" [ids_sym.(0)]
    | Mutual ->
       Tacinterp.interp (apply_tactic "msolve_compare_spec" [using_sym])
  in
  do_proofs goals comparespectactic

let mprove_OrderedType k mind =
  let ids = Array.map (fun body -> body.mind_typename) mind.mind_packets in
  mprove_compare_spec k ids mind;
  let prove_ot i body =
    let id_ot = add_suffix ids.(i) "_OrderedType" in
    let ot =
      CAst.make @@ CAppExpl ((None, build_ot_ref, None),
			     [hole; hole; hole;
			      mkIdentC (add_suffix ids.(i) "_eq_Equivalence");
			      mkIdentC (add_suffix ids.(i) "_lt_StrictOrder");
			      hole;
			      mkIdentC (add_suffix ids.(i) "_compare_spec")]) in
    let tc = Typeclasses.class_info (Coqlib.find_reference
				       "containersplugin"
				       ["Containers";"OrderedType"] "OrderedType")
    in declare_definition id_ot
			  (Decl_kinds.Global, false, Decl_kinds.Definition)
			  None [] None ot None
			  (Lemmas.mk_hook (fun loc gr ->
					   API.Typeclasses.add_instance
					     (API.Typeclasses.new_instance tc Hints.empty_hint_info
									   (loc=Decl_kinds.Local) false gr)))
  in
  Array.iteri prove_ot mind.mind_packets

let generate_mutual_ot gref =
  Coqlib.check_required_library ["Coq";"Classes";"Equivalence"];
  Coqlib.check_required_library ["Containers";"Tactics"];
  let gindref = Nametab.global gref in
  let indconstr = Universes.constr_of_global gindref in
  (* retrieve the inductive type *)
  let env = Global.env () in
  let evd = Evd.from_env env in
  let ind =
    Inductiveops.find_rectype env evd (EConstr.of_constr indconstr) in
  let (mind, _) = Global.lookup_inductive (Globnames.destIndRef gindref) in
  let masks = make_masks mind in
  (*Array.iteri (fun i mask ->
		 fprintf std_formatter "Mask %d :\n" i;
		 List.iter
		   (fun paths ->
		      List.iter (fun b -> fprintf std_formatter "%d " b)
			paths;
		      fprintf std_formatter "\n"
		   ) mask) masks;*)
  let kind =
    if mind.mind_ntypes > 1 then Mutual
    else
      if List.for_all (List.for_all (fun b -> b = -1)) masks.(0) then
	Simple
      else
	Recursive
  in
  if_verbose Feedback.msg_notice (str "Inductive kind : " ++ pr_kind kind);
  (* define the equality predicate *)
  let mutual_eq = mmake_eq_mutual ind masks mind in
  Command.do_mutual_inductive mutual_eq false false false Decl_kinds.Finite;
  (* prove the Equivalence instance *)
  mprove_Equivalence kind mind;
  (* define the strict ordering predicate *)
  let mutual_lt = mmake_lt_mutual ind masks mind in
  Command.do_mutual_inductive mutual_lt false false false Decl_kinds.Finite;
  (* prove the StrictOrder instance *)
  mprove_StrictOrder kind mind;
  (* define the comparison function *)
  mmake_cmp_def kind ind masks mind;
  (* provide the OrderedType instance *)
  mprove_OrderedType kind mind

let generate_ot = generate_mutual_ot

let generate_scheme gref =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let gindref = Nametab.global gref in
  let (evd', indconstr) = Evarutil.new_global evd gindref in
  let (n, _) = Ind_tables.find_scheme
		 Elimschemes.case_dep_scheme_kind_from_prop (fst (destInd evd' indconstr))
  in Feedback.msg_notice (Names.pr_con n ++ str " is defined.")

let print_paths gref =
  let (mind, ibody) = Global.lookup_inductive (Globnames.destIndRef gref) in
    if_verbose Feedback.msg_notice
      (str "Params :" ++ (int mind.mind_nparams));
    if_verbose Feedback.msg_notice
      (str "Recursively uniform params :" ++ (int mind.mind_nparams_rec));
    if_verbose Feedback.msg_notice
      (str "Real arguments :" ++ (int ibody.mind_nrealargs));
  Array.iteri
    (fun i body ->
       let id = Names.Id.to_string body.mind_typename in
       let pptree =
	 Rtree.pp_tree print_recarg body.mind_recargs in
	 if_verbose Feedback.msg_notice (str id);
	 if_verbose Feedback.msg_notice pptree)
    mind.mind_packets


(* Syntax extensions *)

DECLARE PLUGIN "containers_plugin"

(* The 3 next commands are for debug *)
VERNAC COMMAND EXTEND GenerateSimpleOrderedType CLASSIFIED AS SIDEFF
 ["Generate" "Simple" "OrderedType" global(indref)] ->
  [ generate_simple_ot indref ]
    END

VERNAC COMMAND EXTEND GenerateRecursiveOrderedType CLASSIFIED AS SIDEFF
 ["Generate" "Recursive" "OrderedType" global(indref)] ->
  [ generate_rec_ot indref ]
END

VERNAC COMMAND EXTEND GenerateMutualOrderedType CLASSIFIED AS SIDEFF
 ["Generate" "Mutual" "OrderedType" global(indref)] ->
  [ generate_mutual_ot indref ]
END
(* *)

VERNAC COMMAND EXTEND GenerateOrderedType CLASSIFIED AS SIDEFF
 ["Generate" "OrderedType" global(indref)] ->
  [ generate_ot indref ]
END

VERNAC COMMAND EXTEND GenerateScheme CLASSIFIED AS SIDEFF
 ["Generate" "Scheme" global(indref)] ->
   [ let _ = generate_scheme indref in () ]
END

VERNAC COMMAND EXTEND PrintWPaths CLASSIFIED AS QUERY
 ["Print" "Paths" global(indref)] ->
   [ print_paths (Nametab.global indref) ]
END
