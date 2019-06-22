open Z3
open Z3.Boolean
open Z3.Expr
open Z3.Symbol
open Z3.FuncDecl
open Z3.Sort
open Z3.Quantifier
open Z3.Arithmetic

module NamedDecl = Context.Named.Declaration

let msg_in_tactic str : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
    Feedback.msg_warning (Pp.str str)))


let printHello : unit Proofview.tactic =
  let open Proofview.Notations in
  msg_in_tactic "hello" >>= fun () ->
  Tacticals.New.tclIDTAC


let smt : unit Proofview.tactic = 
  let open Proofview.Notations in
  msg_in_tactic Version.to_string >>= fun () ->
  Tacticals.New.tclIDTAC 


let constr2str env sigma term = 
  Pp.string_of_ppcmds @@ Printer.pr_constr_env env sigma term


let euclid_smt : unit Proofview.tactic = 


  let cfg = [("model", "true"); ("proof", "true"); ("model_validate", "true"); ("well_sorted_check", "true")] in
  let ctx = mk_context cfg in

  let bool_sort = mk_sort ctx in
  let real_sort = Arithmetic.Real.mk_sort ctx in

  let point_sym = mk_string ctx "Point" in
  let point_sort = mk_uninterpreted ctx point_sym in
  let line_sym = mk_string ctx "Line" in
  let line_sort = mk_uninterpreted ctx line_sym in
  let circle_sym = mk_string ctx "Circle" in
  let circle_sort = mk_uninterpreted ctx circle_sym in

  let between_sym = mk_string ctx "Between" in
  let between_func = mk_func_decl ctx between_sym [point_sort; point_sort; point_sort] bool_sort in
  let on_l_sym = mk_string ctx "On_L" in
  let on_l_func = mk_func_decl ctx on_l_sym [point_sort; line_sort] bool_sort in
  let on_c_sym = mk_string ctx "On_C" in
  let on_c_func = mk_func_decl ctx on_c_sym [point_sort; circle_sort] bool_sort in
  let inside_sym = mk_string ctx "Inside" in
  let inside_func = mk_func_decl ctx inside_sym [point_sort; circle_sort] bool_sort in
  let center_sym = mk_string ctx "Center" in
  let center_func = mk_func_decl ctx center_sym [point_sort; circle_sort] bool_sort in
  let sameside_sym = mk_string ctx "SameSide" in
  let sameside_func = mk_func_decl ctx sameside_sym [point_sort; point_sort; line_sort] bool_sort in
  let intersects_ll_sym = mk_string ctx "Intersects_LL" in
  let intersects_ll_func = mk_func_decl ctx intersects_ll_sym [line_sort; line_sort] bool_sort in
  let intersects_lc_sym = mk_string ctx "Intersects_LC" in
  let intersects_lc_func = mk_func_decl ctx intersects_lc_sym [line_sort; circle_sort] bool_sort in
  let intersects_cc_sym = mk_string ctx "Intersects_CC" in
  let intersects_cc_func = mk_func_decl ctx intersects_cc_sym [circle_sort; circle_sort] bool_sort in

  let segment_pp_sym = mk_string ctx "Segment_PP" in
  let segment_pp_func = mk_func_decl ctx segment_pp_sym [point_sort; point_sort] real_sort in
  let angle_ppp_sym = mk_string ctx "Angle_PPP" in
  let angle_ppp_func = mk_func_decl ctx angle_ppp_sym [point_sort; point_sort; point_sort] real_sort in
  let area_ppp_sym = mk_string ctx "Area_PPP" in
  let area_ppp_func = mk_func_decl ctx area_ppp_sym [point_sort; point_sort; point_sort] real_sort in
  let rightangle_sym = mk_string ctx "RightAngle" in
  let rightangle_const = FuncDecl.mk_const_decl ctx rightangle_sym real_sort in

  let sort_names = [point_sym; line_sym; circle_sym] in
  let sorts = [point_sort; line_sort; circle_sort] in
  let decl_names = [between_sym; on_l_sym; on_c_sym; inside_sym; center_sym; sameside_sym; intersects_ll_sym; intersects_lc_sym; intersects_cc_sym; segment_pp_sym; angle_ppp_sym; area_ppp_sym; rightangle_sym] in
  let decls = [between_func; on_l_func; on_c_func; inside_func; center_func; sameside_func; intersects_ll_func; intersects_lc_func; intersects_cc_func; segment_pp_func; angle_ppp_func; area_ppp_func; rightangle_const] in

  let assertions = AST.ASTVector.to_expr_list 
    (SMT.parse_smtlib2_file ctx "/Users/yangky/Desktop/Research/Project-A/system-e/src/e.smt2" 
      sort_names sorts decl_names decls) in

  let solver = Solver.mk_solver ctx None in
  let solver_param = Params.mk_params ctx in
  Params.add_symbol solver_param (mk_string ctx "logic") (mk_string ctx "AUFLIRA");
  Solver.set_parameters solver solver_param;
  Solver.add solver assertions;
  

  let constr2sort term = 
    match Constr.kind term with
    | Const (constant, _) -> 
        let constant_str = Names.Label.to_string @@ Names.Constant.label constant in
        (match constant_str with
        | "Point" -> point_sort
        | "Line" -> line_sort
        | "Circle" -> circle_sort
        | _ -> failwith "")
    | _ -> failwith ""
  in


  let rec constr2expr env sigma term constants binders ctx = 
    let recur t = constr2expr env sigma t constants binders ctx in

    (*
    print_endline "\n\n**********************";
    List.iter (fun (id, const) -> print_endline id) constants;
    print_endline "----------------------";
    print_endline ("constr2expr: " ^ (constr2str env sigma term));
    *)
    match Constr.kind term with
    | Rel idx ->
        (*
        print_endline "Rel"; 
        print_endline @@ string_of_int idx;
        print_endline @@ string_of_int (List.length binders);*)
        let binder_idx = (List.length binders) - idx in
        (match List.nth binders binder_idx with
        | None -> failwith ""
        | Some sort ->
            let debruijn_idx = List.fold_left (+) 0 
                                (List.mapi (fun i s -> if i > binder_idx then
                                                        match s with 
                                                        | None -> 0
                                                        | Some _ -> 1
                                                        else 0) binders) 
            in
            mk_bound ctx debruijn_idx sort)

    | Var id ->
        (*print_endline "Var";*) 
        let id_str = Names.Id.to_string id in
        List.assoc id_str constants

    | Meta _ -> print_endline "Meta"; mk_fresh_const ctx "Meta" (mk_sort ctx)
    | Evar _ -> print_endline "Evar"; mk_fresh_const ctx "Evar" (mk_sort ctx)
    | Sort _ -> print_endline "Sort"; mk_fresh_const ctx "Rel" (mk_sort ctx)
    | Cast _ -> print_endline "Cast"; mk_fresh_const ctx "Rel" (mk_sort ctx)

    | Prod (name, t1, t2) -> 
        (*print_endline "Prod"; *)
        (match name with
        | Anonymous -> 
            mk_implies ctx (recur t1) (constr2expr env sigma t2 constants (binders @ [None]) ctx)
        | Name id ->
            let id_str = Names.Id.to_string id in
            let sort = constr2sort t1 in
            expr_of_quantifier @@ mk_forall ctx [sort] [mk_string ctx id_str]
              (constr2expr env sigma t2 constants (binders @ [Some sort]) ctx) None [] [] None None)

    | Lambda (name, t, body) -> (* existential quantifiers *)
        (*print_endline "Lambda";*)
        (match name with
        | Anonymous -> recur body
        | Name id -> 
            let id_str = Names.Id.to_string id in
            let sort = constr2sort t in
            expr_of_quantifier @@ mk_exists ctx [sort] [mk_string ctx id_str] 
              (constr2expr env sigma body constants (binders @ [Some sort]) ctx) None [] [] None None)

    | LetIn _ -> print_endline "LetIn"; mk_fresh_const ctx "Rel" (mk_sort ctx)

    | App (func, args) -> 
        (* print_endline "App"; 
        
        print_endline (constr2str env sigma func);
        Array.iter (fun t -> print_endline (constr2str env sigma t)) args;
        *)
        let func_str = constr2str env sigma func in
        (match func_str with
        | "not" -> 
            mk_not ctx (recur (Array.get args 0))
        | "@eq" -> 
            mk_eq ctx (recur (Array.get args 1)) (recur (Array.get args 2))
        | "ex" ->
            recur (Array.get args 1)
        | "and" -> 
            mk_and ctx [recur (Array.get args 0); recur (Array.get args 1)]
        | "Rplus" ->
            mk_add ctx [recur (Array.get args 0); recur (Array.get args 1)]
        | "segment2real" -> 
            recur (Array.get args 0)
        | "Segment_PP" -> 
            mk_app ctx segment_pp_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "On_L" ->
            mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "SameSide" ->
            mk_app ctx sameside_func [recur (Array.get args 0); recur (Array.get args 1); recur (Array.get args 2)]
        | "Between" ->
            mk_app ctx between_func [recur (Array.get args 0); recur (Array.get args 1); recur (Array.get args 2)]
        | "On_C" ->
            mk_app ctx on_c_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "Inside" ->
            mk_app ctx inside_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "Center" ->
            mk_app ctx center_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "Intersects_LL" ->
            mk_app ctx intersects_ll_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "Intersects_LC" ->
            mk_app ctx intersects_lc_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "Intersects_CC" ->
            mk_app ctx intersects_cc_func [recur (Array.get args 0); recur (Array.get args 1)]
        | _ -> failwith func_str)

    | Const _ -> print_endline "Const"; mk_fresh_const ctx "Const" (mk_sort ctx)
    | Ind _ -> print_endline "Ind"; mk_fresh_const ctx "Ind" (mk_sort ctx)
    | Construct _ -> print_endline "Construct"; mk_fresh_const ctx "Construct" (mk_sort ctx)
    | Case _ -> print_endline "Case"; mk_fresh_const ctx "Case" (mk_sort ctx)
    | Fix _ -> print_endline "Fix"; mk_fresh_const ctx "Fix" (mk_sort ctx)
    | CoFix _ -> print_endline "CoFix"; mk_fresh_const ctx "CoFix" (mk_sort ctx)
    | Proj _ -> print_endline "Proj"; mk_fresh_const ctx "Proj" (mk_sort ctx)
  in


  Proofview.Goal.enter begin fun gl ->

  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = EConstr.to_constr sigma (Proofview.Goal.concl gl) in

  let hyps = Proofview.Goal.hyps gl in

  let constants = List.fold_right (fun decl constants -> 
    let t = EConstr.to_constr sigma (NamedDecl.get_type decl) in
    let id_str = Names.Id.to_string (NamedDecl.get_id decl) in   
    let t_str = constr2str env sigma t in
    (*print_endline (id_str ^ " : " ^ t_str);*)
    match t_str with
    | "Point" -> (id_str, mk_const ctx (mk_string ctx id_str) point_sort) :: constants
    | "Line" -> (id_str, mk_const ctx (mk_string ctx id_str) line_sort) :: constants
    | "Circle" -> (id_str, mk_const ctx (mk_string ctx id_str) circle_sort) :: constants
    | _ -> 
        let assertion = constr2expr env sigma t constants [] ctx in
        Solver.add solver [assertion];
        constants
  ) hyps [] in

  (*print_endline (constr2str env sigma concl);*)
  let negated_concl = mk_not ctx (constr2expr env sigma concl constants [] ctx) in
  Solver.add solver [negated_concl];

  (*let all_assertions = Solver.get_assertions solver in
  List.iter (fun ass -> print_endline @@ Expr.to_string ass) all_assertions;

  print_endline "Solving SMT..";*)
  let res = Solver.check solver [] in
  match res with
  |	UNSATISFIABLE ->
      print_endline "UNSAT";
      (match Solver.get_proof solver with
      | None -> failwith "" 
      | Some proof ->
          (*print_endline @@ Expr.to_string proof;*)
          let open Proofview.Notations in
          msg_in_tactic "tactic return" >>= fun () -> Tacticals.New.tclIDTAC)
  | UNKNOWN -> 
      print_endline "UNKNOWN";
      failwith "UNKNOWN"
  |	SATISFIABLE -> 
      print_endline "SAT";
      failwith "SATISFIABLE"
  end

