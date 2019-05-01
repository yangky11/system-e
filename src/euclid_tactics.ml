open Z3

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


let econstr2assertion env sigma term = 
  Pp.string_of_ppcmds @@ Printer.pr_econstr_env env sigma term


let euclid_smt : unit Proofview.tactic = 
  let cfg = [("model", "true"); ("proof", "true"); ("model_validate", "true"); ("well_sorted_check", "true")] in
  let ctx = mk_context cfg in

  let bool_sort = Boolean.mk_sort ctx in
  let real_sort = Arithmetic.Real.mk_sort ctx in

  let point_sym = Symbol.mk_string ctx "Point" in
  let point_sort = Sort.mk_uninterpreted ctx point_sym in
  let line_sym = Symbol.mk_string ctx "Line" in
  let line_sort = Sort.mk_uninterpreted ctx line_sym in
  let circle_sym = Symbol.mk_string ctx "Circle" in
  let circle_sort = Sort.mk_uninterpreted ctx circle_sym in

  let between_sym = Symbol.mk_string ctx "Between" in
  let between_func = FuncDecl.mk_func_decl ctx between_sym [point_sort; point_sort; point_sort] bool_sort in
  let on_l_sym = Symbol.mk_string ctx "On_L" in
  let on_l_func = FuncDecl.mk_func_decl ctx on_l_sym [point_sort; line_sort] bool_sort in
  let on_c_sym = Symbol.mk_string ctx "On_C" in
  let on_c_func = FuncDecl.mk_func_decl ctx on_c_sym [point_sort; circle_sort] bool_sort in
  let inside_sym = Symbol.mk_string ctx "Inside" in
  let inside_func = FuncDecl.mk_func_decl ctx inside_sym [point_sort; circle_sort] bool_sort in
  let center_sym = Symbol.mk_string ctx "Center" in
  let center_func = FuncDecl.mk_func_decl ctx center_sym [point_sort; circle_sort] bool_sort in
  let sameside_sym = Symbol.mk_string ctx "SameSide" in
  let sameside_func = FuncDecl.mk_func_decl ctx sameside_sym [point_sort; point_sort; line_sort] bool_sort in
  let intersects_ll_sym = Symbol.mk_string ctx "Intersects_LL" in
  let intersects_ll_func = FuncDecl.mk_func_decl ctx intersects_ll_sym [line_sort; line_sort] bool_sort in
  let intersects_lc_sym = Symbol.mk_string ctx "Intersects_LC" in
  let intersects_lc_func = FuncDecl.mk_func_decl ctx intersects_lc_sym [line_sort; circle_sort] bool_sort in
  let intersects_cc_sym = Symbol.mk_string ctx "Intersects_CC" in
  let intersects_cc_func = FuncDecl.mk_func_decl ctx intersects_cc_sym [circle_sort; circle_sort] bool_sort in

  let segment_pp_sym = Symbol.mk_string ctx "Segment_PP" in
  let segment_pp_func = FuncDecl.mk_func_decl ctx segment_pp_sym [point_sort; point_sort] real_sort in
  let angle_ppp_sym = Symbol.mk_string ctx "Angle_PPP" in
  let angle_ppp_func = FuncDecl.mk_func_decl ctx angle_ppp_sym [point_sort; point_sort; point_sort] real_sort in
  let area_ppp_sym = Symbol.mk_string ctx "Area_PPP" in
  let area_ppp_func = FuncDecl.mk_func_decl ctx area_ppp_sym [point_sort; point_sort; point_sort] real_sort in
  let rightangle_sym = Symbol.mk_string ctx "RightAngle" in
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
  Params.add_symbol solver_param (Symbol.mk_string ctx "logic") (Symbol.mk_string ctx "AUFLIRA");
  Solver.set_parameters solver solver_param;
  Solver.add solver assertions;
  
  Proofview.Goal.enter begin fun gl ->

  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let goal_str = econstr2assertion env sigma concl in

  let hyps = Proofview.Goal.hyps gl in
  let rec hyps2assertion = function
  | [] -> ""
  | decl::rest -> 
      let t = NamedDecl.get_type decl in
      let id = NamedDecl.get_id decl in
      ((Names.Id.to_string id) ^ " : " ^ (econstr2assertion env sigma t)) ^ "\n" ^ (hyps2assertion rest)
      
  in
  let hyps_str = hyps2assertion hyps in

  let res = Solver.check solver [] in
  match res with
  |	Solver.UNSATISFIABLE -> failwith "UNSAT"
  |	Solver.UNKNOWN -> failwith "UNKNOWN"
  |	Solver.SATISFIABLE ->
      let open Proofview.Notations in
      msg_in_tactic (goal_str ^ "\n---------\n" ^ hyps_str) >>= fun () -> Tacticals.New.tclIDTAC 

  end

