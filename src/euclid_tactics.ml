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
  print_endline "initializing euclid_smt..";

  let cfg = [("timeout", "180000"); ("auto_config", "true"); ("model", "false"); ("proof", "false"); ("model_validate", "false"); ("well_sorted_check", "false")] in
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
  let on_l_sym = mk_string ctx "OnL" in
  let on_l_func = mk_func_decl ctx on_l_sym [point_sort; line_sort] bool_sort in
  let on_c_sym = mk_string ctx "OnC" in
  let on_c_func = mk_func_decl ctx on_c_sym [point_sort; circle_sort] bool_sort in
  let inside_sym = mk_string ctx "Inside" in
  let inside_func = mk_func_decl ctx inside_sym [point_sort; circle_sort] bool_sort in
  let center_sym = mk_string ctx "Center" in
  let center_func = mk_func_decl ctx center_sym [point_sort; circle_sort] bool_sort in
  let sameside_sym = mk_string ctx "SameSide" in
  let sameside_func = mk_func_decl ctx sameside_sym [point_sort; point_sort; line_sort] bool_sort in
  let intersects_ll_sym = mk_string ctx "IntersectsLL" in
  let intersects_ll_func = mk_func_decl ctx intersects_ll_sym [line_sort; line_sort] bool_sort in
  let intersects_lc_sym = mk_string ctx "IntersectsLC" in
  let intersects_lc_func = mk_func_decl ctx intersects_lc_sym [line_sort; circle_sort] bool_sort in
  let intersects_cc_sym = mk_string ctx "IntersectsCC" in
  let intersects_cc_func = mk_func_decl ctx intersects_cc_sym [circle_sort; circle_sort] bool_sort in

  let segment_pp_sym = mk_string ctx "SegmentPP" in
  let segment_pp_func = mk_func_decl ctx segment_pp_sym [point_sort; point_sort] real_sort in
  let angle_ppp_sym = mk_string ctx "AnglePPP" in
  let angle_ppp_func = mk_func_decl ctx angle_ppp_sym [point_sort; point_sort; point_sort] real_sort in
  let area_ppp_sym = mk_string ctx "AreaPPP" in
  let area_ppp_func = mk_func_decl ctx area_ppp_sym [point_sort; point_sort; point_sort] real_sort in
  let rightangle_sym = mk_string ctx "RightAngle" in
  let rightangle_const = FuncDecl.mk_const_decl ctx rightangle_sym real_sort in

  let sort_names = [point_sym; line_sym; circle_sym] in
  let sorts = [point_sort; line_sort; circle_sort] in
  let decl_names = [between_sym; on_l_sym; on_c_sym; inside_sym; center_sym; sameside_sym; intersects_ll_sym; intersects_lc_sym; intersects_cc_sym; segment_pp_sym; angle_ppp_sym; area_ppp_sym; rightangle_sym] in
  let decls = [between_func; on_l_func; on_c_func; inside_func; center_func; sameside_func; intersects_ll_func; intersects_lc_func; intersects_cc_func; segment_pp_func; angle_ppp_func; area_ppp_func; rightangle_const] in

  let background_theory = AST.ASTVector.to_expr_list 
    (SMT.parse_smtlib2_file ctx "/Users/yangky/Desktop/Research/Project-A/system-e/src/e.smt2" 
      sort_names sorts decl_names decls) in

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

    match Constr.kind term with
    | Rel idx ->
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
        let id_str = Names.Id.to_string id in
        List.assoc id_str constants

    | Meta _ -> failwith "Meta"
    | Evar _ -> failwith "Evar"
    | Sort _ -> failwith "Sort"
    | Cast _ -> failwith "Cast"

    | Prod (name, t1, t2) -> 
        (match name.binder_name with
        | Anonymous -> 
            mk_implies ctx (recur t1) (constr2expr env sigma t2 constants (binders @ [None]) ctx)
        | Name id ->
            let id_str = Names.Id.to_string id in
            let sort = constr2sort t1 in
            expr_of_quantifier @@ mk_forall ctx [sort] [mk_string ctx id_str]
              (constr2expr env sigma t2 constants (binders @ [Some sort]) ctx) None [] [] None None)

    | Lambda (name, t, body) -> (* existential quantifiers *)
        (match name.binder_name with
        | Anonymous -> recur body
        | Name id -> 
            let id_str = Names.Id.to_string id in
            let sort = constr2sort t in
            expr_of_quantifier @@ mk_exists ctx [sort] [mk_string ctx id_str] 
              (constr2expr env sigma body constants (binders @ [Some sort]) ctx) None [] [] None None)

    | LetIn _ -> failwith "LetIn"

    | App (func, args) -> 
        print_endline "App"; 
        print_endline (constr2str env sigma func);
        Array.iter (fun t -> print_endline (constr2str env sigma t)) args;
        let func_str = constr2str env sigma func in
        (match func_str with
        | "not" -> 
            mk_not ctx (recur (Array.get args 0))
        | "@eq" -> 
            mk_eq ctx (recur (Array.get args 1)) (recur (Array.get args 2))
        | "Rgt" ->
            mk_gt ctx (recur (Array.get args 0)) (recur (Array.get args 1))
        | "Rge" ->
            mk_ge ctx (recur (Array.get args 0)) (recur (Array.get args 1))
        | "Rlt" ->
            mk_lt ctx (recur (Array.get args 0)) (recur (Array.get args 1))
        | "Rle" ->
            mk_le ctx (recur (Array.get args 0)) (recur (Array.get args 1))
        | "ex" ->
            recur (Array.get args 1)
        | "and" -> 
            mk_and ctx [recur (Array.get args 0); recur (Array.get args 1)]
        | "or" ->
            mk_or ctx [recur (Array.get args 0); recur (Array.get args 1)]
        | "Rplus" ->
            mk_add ctx [recur (Array.get args 0); recur (Array.get args 1)]
        | "Rmult" ->
            mk_mul ctx  [recur (Array.get args 0); recur (Array.get args 1)]
        | "IZR" ->
            Integer.mk_int2real ctx (recur (Array.get args 0))
        | "segment2real"
        | "segment2real_implicit"
        | "angle2real"
        | "angle2real_implicit"
        | "area2real"
        | "area2real_implicit" ->
            recur (Array.get args 0)
        | "SegmentPP" -> 
            mk_app ctx segment_pp_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "AnglePPP" -> 
            mk_app ctx angle_ppp_func [recur (Array.get args 0); recur (Array.get args 1); recur (Array.get args 2)]
        | "AreaPPP" -> 
            mk_app ctx area_ppp_func [recur (Array.get args 0); recur (Array.get args 1); recur (Array.get args 2)]
        | "OnL" ->
            mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "SameSide" ->
            mk_app ctx sameside_func [recur (Array.get args 0); recur (Array.get args 1); recur (Array.get args 2)]
        | "OppositeSide" ->
            let a_on_L = mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 2)] in
            let b_on_L = mk_app ctx on_l_func [recur (Array.get args 1); recur (Array.get args 2)] in
            let a_sameside_b = mk_app ctx sameside_func [recur (Array.get args 0); recur (Array.get args 1); recur (Array.get args 2)] in
            mk_and ctx [mk_not ctx a_on_L; mk_not ctx b_on_L; mk_not ctx a_sameside_b]
        | "Between" ->
            mk_app ctx between_func [recur (Array.get args 0); recur (Array.get args 1); recur (Array.get args 2)]
        | "OnC" ->
            mk_app ctx on_c_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "Inside" ->
            mk_app ctx inside_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "Outside" ->
            let a_inside_alpha = mk_app ctx inside_func [recur (Array.get args 0); recur (Array.get args 1)] in
            let a_on_alpha = mk_app ctx on_c_func [recur (Array.get args 0); recur (Array.get args 1)] in
            mk_and ctx [mk_not ctx a_inside_alpha; mk_not ctx a_on_alpha]
        | "DistinctPointsOnL" ->
            let a_neq_b = mk_not ctx (mk_eq ctx (recur (Array.get args 0)) (recur (Array.get args 1))) in
            let a_on_L = mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 2)] in
            let b_on_L = mk_app ctx on_l_func [recur (Array.get args 1); recur (Array.get args 2)] in
            mk_and ctx [a_neq_b; a_on_L; b_on_L]
        | "Triangle" ->
            let a_neq_b = mk_not ctx (mk_eq ctx (recur (Array.get args 0)) (recur (Array.get args 1))) in
            let a_on_AB = mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 3)] in
            let b_on_AB = mk_app ctx on_l_func [recur (Array.get args 1); recur (Array.get args 3)] in
            let b_on_BC = mk_app ctx on_l_func [recur (Array.get args 1); recur (Array.get args 4)] in
            let c_on_BC = mk_app ctx on_l_func [recur (Array.get args 2); recur (Array.get args 4)] in
            let c_on_CA = mk_app ctx on_l_func [recur (Array.get args 2); recur (Array.get args 5)] in
            let a_on_CA = mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 5)] in
            let ab_neq_bc = mk_not ctx (mk_eq ctx (recur (Array.get args 3)) (recur (Array.get args 4))) in
            let bc_neq_ca = mk_not ctx (mk_eq ctx (recur (Array.get args 4)) (recur (Array.get args 5))) in
            let ca_neq_ab = mk_not ctx (mk_eq ctx (recur (Array.get args 5)) (recur (Array.get args 3))) in
            mk_and ctx [a_neq_b; a_on_AB; b_on_AB; b_on_BC; c_on_BC; c_on_CA; a_on_CA; ab_neq_bc; bc_neq_ca; ca_neq_ab]
        | "RectilinearAngle" ->
            let a_neq_b = mk_not ctx (mk_eq ctx (recur (Array.get args 0)) (recur (Array.get args 1))) in
            let a_on_ab = mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 3)] in
            let b_on_ab = mk_app ctx on_l_func [recur (Array.get args 1); recur (Array.get args 3)] in
            let b_neq_c = mk_not ctx (mk_eq ctx (recur (Array.get args 1)) (recur (Array.get args 2))) in
            let b_on_bc = mk_app ctx on_l_func [recur (Array.get args 1); recur (Array.get args 4)] in
            let c_on_bc = mk_app ctx on_l_func [recur (Array.get args 2); recur (Array.get args 4)] in
            mk_and ctx [a_neq_b; a_on_ab; b_on_ab; b_neq_c; b_on_bc; c_on_bc]
        | "Parallelogram" ->
            let a_on_AB = mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 4)] in
            let b_on_AB = mk_app ctx on_l_func [recur (Array.get args 1); recur (Array.get args 4)] in
            let c_on_CD = mk_app ctx on_l_func [recur (Array.get args 2); recur (Array.get args 5)] in
            let d_on_CD = mk_app ctx on_l_func [recur (Array.get args 3); recur (Array.get args 5)] in
            let a_on_AC = mk_app ctx on_l_func [recur (Array.get args 0); recur (Array.get args 6)] in
            let c_on_AC = mk_app ctx on_l_func [recur (Array.get args 2); recur (Array.get args 6)] in
            let b_neq_d = mk_not ctx (mk_eq ctx (recur (Array.get args 1)) (recur (Array.get args 3))) in
            let b_on_BD = mk_app ctx on_l_func [recur (Array.get args 1); recur (Array.get args 7)] in
            let d_on_BD = mk_app ctx on_l_func [recur (Array.get args 3); recur (Array.get args 7)] in
            let ac_sameside_bd = mk_app ctx sameside_func [recur (Array.get args 0); recur (Array.get args 2); recur (Array.get args 7)] in
            let ab_parallel_cd = mk_not ctx (mk_app ctx intersects_ll_func [recur (Array.get args 4); recur (Array.get args 5)]) in
            let ac_parallel_bd = mk_not ctx (mk_app ctx intersects_ll_func [recur (Array.get args 6); recur (Array.get args 7)]) in
            mk_and ctx [a_on_AB; b_on_AB; c_on_CD; d_on_CD; a_on_AC; c_on_AC; b_neq_d; b_on_BD; d_on_BD; ac_sameside_bd; ab_parallel_cd; ac_parallel_bd]
        | "Center" ->
            mk_app ctx center_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "IntersectsLL" ->
            mk_app ctx intersects_ll_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "IntersectsLC" ->
            mk_app ctx intersects_lc_func [recur (Array.get args 0); recur (Array.get args 1)]
        | "IntersectsCC" ->
            mk_app ctx intersects_cc_func [recur (Array.get args 0); recur (Array.get args 1)]
        | _ -> failwith func_str)

    | Const _ -> failwith "Const"

    | Ind ((induct, _), _) -> 
        let s = Names.MutInd.to_string induct in
        (match s with
        | "Coq.Init.Logic.False" -> mk_false ctx
        | "Coq.Init.Logic.True" -> mk_true ctx
        | _ -> failwith "Ind")

    | Construct (((induct, _), idx), _) ->  
        let s = Names.MutInd.to_string induct in
        (match s, idx with
        | "SystemE.Sorts.Angle", 2 -> mk_app ctx rightangle_const []
        | "Coq.Numbers.BinNums.Z", 1 -> Integer.mk_numeral_i ctx 0 
        | _ -> failwith "Construct")

    | Case _ -> failwith "Case"
    | Fix _ -> failwith "Fix"
    | CoFix _ -> failwith "CoFix"
    | Proj _ -> failwith "Proj"
    | Int _ -> failwith "Int"
    | Float _ -> failwith "Float"
  in


  Proofview.Goal.enter begin fun gl ->
  print_endline "calling euclid_smt..";
  
  let solver = Solver.mk_solver ctx None in
  Solver.add solver background_theory;

  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = EConstr.to_constr sigma (Proofview.Goal.concl gl) in

  let hyps = Proofview.Goal.hyps gl in

  let constants = List.fold_right (fun decl constants -> 
    let t = EConstr.to_constr sigma (NamedDecl.get_type decl) in
    let id_str = Names.Id.to_string (NamedDecl.get_id decl) in   
    let t_str = constr2str env sigma t in
    match t_str with
    | "Point" -> (id_str, mk_const ctx (mk_string ctx id_str) point_sort) :: constants
    | "Line" -> (id_str, mk_const ctx (mk_string ctx id_str) line_sort) :: constants
    | "Circle" -> (id_str, mk_const ctx (mk_string ctx id_str) circle_sort) :: constants
    | _ -> 
        let assertion = constr2expr env sigma t constants [] ctx in
        Solver.add solver [assertion];
        constants
  ) hyps [] in

  let negated_concl = mk_not ctx (constr2expr env sigma concl constants [] ctx) in
  Solver.add solver [negated_concl];

  let all_assertions = Solver.get_assertions solver in
  List.iter (fun ass -> print_endline ("(assert\n" ^ Expr.to_string ass ^ "\n)")) all_assertions;
  
  let solver_param = Params.mk_params ctx in
  Params.add_bool solver_param (mk_string ctx "smt.mbqi") true;
  Params.add_bool solver_param (mk_string ctx "smt.ematching") true;
  Params.add_bool solver_param (mk_string ctx "smt.mbqi.trace") true;
  Params.add_int solver_param (mk_string ctx "smt.mbqi.max_cexs") 1;
  Params.add_int solver_param (mk_string ctx "smt.mbqi.force_template") 0;
  Params.add_bool solver_param (mk_string ctx "smt.qi.profile") true;
  Params.add_float solver_param (mk_string ctx "smt.qi.eager_threshold") 10.0;
  Params.add_int solver_param (mk_string ctx "smt.qi.max_multi_patterns") 4;
  Solver.set_parameters solver solver_param;

  print_endline "Solving SMT..";
  let open Proofview.Notations in
  match Solver.check solver [] with
  |	UNSATISFIABLE ->
      print_endline "UNSAT";
      msg_in_tactic "tactic return" >>= fun () -> Tacticals.New.tclIDTAC
  | UNKNOWN -> 
      let solver_param = Params.mk_params ctx in
      Params.add_float solver_param (mk_string ctx "smt.qi.eager_threshold") 0.5;
      Solver.set_parameters solver solver_param;
      print_endline "Retrying..";
      (match Solver.check solver [] with
      | UNSATISFIABLE ->
          print_endline "UNSAT";
          msg_in_tactic "tactic return" >>= fun () -> Tacticals.New.tclIDTAC
      | UNKNOWN ->
          print_endline "UNKNOWN";
          Tacticals.New.tclFAIL 1000 (Pp.str "UNKNOWN")
      |	SATISFIABLE -> 
          print_endline "SAT";
          Tacticals.New.tclFAIL 1000 (Pp.str "SAT") 
      )
  |	SATISFIABLE -> 
      print_endline "SAT";
      Tacticals.New.tclFAIL 1000 (Pp.str "SAT")  (* find a suitable error level so that we can capture the error in Coq *)
  end

