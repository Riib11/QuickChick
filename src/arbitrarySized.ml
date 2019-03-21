open Pp
open Util
open GenericLib
open GenLib
open Error
   
(* Derivation of ArbitrarySized. Contains mostly code from derive.ml *)

let rec replace v x = function
  | [] -> []
  | y::ys -> if y = v then x::ys else y::(replace v x ys)

let arbitrarySized_body (ty_ctr : ty_ctr) (ctrs : ctr_rep list) iargs = 
  
  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in
  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in

  let tyParams = List.map gVar (list_drop_every 2 iargs) in

  (* Need reverse fold for this *)
  let create_for_branch tyParams rec_name size (ctr, ty) =
    let rec aux i acc ty : coq_expr =
      match ty with
      | Arrow (ty1, ty2) ->
         bindGen (if isCurrentTyCtr ty1 then
                     gApp (gVar rec_name) [gVar size]
                  else gInject "arbitrary")
           (Printf.sprintf "p%d" i)
           (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
      | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (tyParams @ List.rev acc))
    in aux 0 [] ty in
  
  let bases = List.filter (fun (_, ty) -> isBaseBranch ty) ctrs in

  gRecFunInWithArgs
    "arb_aux" [gArg ~assumName:(gInject "size") ()]
    (fun (aux_arb, [size]) ->
      gMatch (gVar size)
        [(injectCtr "O", [],
          fun _ -> (oneof' (List.map (
                                         fun x -> (gFunTyped [("_tt", gUnit)] (fun _ -> 
                                         create_for_branch tyParams aux_arb size x))) bases)))
        ;(injectCtr "S", ["size'"],
          fun [size'] -> (frequency' (List.map (fun (ctr,ty') ->
                                                   (Weightmap.lookup_weight ctr size',
                                                    gFunTyped [("_tt", gUnit)] (fun _ -> 
                                         create_for_branch tyParams aux_arb size' (ctr,ty')))) ctrs)))
    ])
    (fun x -> gVar x)

exception ConversionError
  
let arbitrarySized_decl ty_ctr ctrs iargs =

  let arb_body = arbitrarySized_body ty_ctr ctrs iargs in
  let arbitrary_decl = gFun ["s"] (fun [s] -> gApp arb_body [gVar s]) in

  debug_coq_expr arb_body;
  gRecord [("arbitrarySized", arbitrary_decl)]

let fuzzy_decl ty_ctr ctrs iargs =

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  
  let tyParams = List.map gVar (list_keep_every 3 iargs) in

  let fuzzy_fun = 
    let fuzzy_body x =

        (* Trying to convert an instance of ctr to ctr'.
           Takes as argument vs (the values of ctr's parameters)
           and converts to ctr' on the fly, producing values for types
           as needed. 
           UP   : ctr  subseq ctr'
           DOWN : ctr' subseq ctr

           INV: length vs = length ty

           Keep a bool on up to track differences to avoid recomputing 
           if similar sigs.
         *)
        
        let rec convert_up b i ctr ty ctr' ty' vs vs_so_far =
          match (ty, ty', vs) with
          | (Arrow (ty1, ty2), Arrow (ty1', ty2'), v::vs) ->
             if ty1 = ty1' then
               (* Same type, just keep the var *)
               convert_up b (i+1) ctr ty2 ctr' ty2' vs (v :: vs_so_far)
             else
               (* Different type, produce arbitrary and recurse *)
               bindGen (gInject "arbitrary") ("param" ^ string_of_int i) (fun v' ->
                   convert_up false (i+1) ctr (Arrow (ty1, ty2)) ctr' ty2' vs (v' :: vs_so_far))
          | (TyCtr _, Arrow (ty1', ty2'), []) ->
             (* Different vars allowed at the end, arbitrary them. *)
             bindGen (gInject "arbitrary") ("param" ^ string_of_int i) (fun v' ->
                 convert_up false (i+1) ctr ty ctr' ty2' [] (v' :: vs_so_far))
          | (TyCtr _, TyCtr _, []) ->
             (* Finished, just produce the new type constructor. *)
             if not b then 
               returnGen (gApp ~explicit:true (gCtr ctr') (tyParams @ (List.map gVar (List.rev vs_so_far))))
             else
             (* Identical sigs, will be handled by convert_down. Raise error. *)
             raise ConversionError
          | _ ->
             (* Something went wrong. Can't convert *)
             raise ConversionError
        in 

        let rec convert_down i ctr ty ctr' ty' vs vs_so_far =
          match (ty, ty', vs) with
          | (Arrow (ty1, ty2), Arrow (ty1', ty2'), v::vs) ->
             if ty1 = ty1' then
               (* Same type, just keep the var *)
               convert_down (i+1) ctr ty2 ctr' ty2' vs (v :: vs_so_far)
             else
               (* Different type, throw away v and recurse *)
               convert_down (i+1) ctr ty2 ctr' (Arrow (ty1', ty2')) vs vs_so_far
          | (Arrow (ty1, ty2), TyCtr _, v :: vs) ->
             (* Different vars allowed at the end for ctr, throw them away. *)
             convert_down (i+1) ctr ty2 ctr' ty' vs vs_so_far
          | (TyCtr _, TyCtr _, []) ->
             (* Finished, just produce the new type constructor. *)
             returnGen (gApp ~explicit:true (gCtr ctr') (tyParams @ (List.map gVar (List.rev vs_so_far))))
          | _ ->
             (* Something went wrong. Can't convert *)
             raise ConversionError
        in 

        (* This should be moved to some util func *)
        let rec catMaybes = function
          | [] -> []
          | Some x :: t -> x :: catMaybes t
          | None :: t -> catMaybes t in
        
        let rec convert_ctr ((ctr, ty)) ctrs vs =
          match ctrs with
          | ((ctr', ty')) :: ctrs' ->
             if ctr == ctr' then convert_ctr ((ctr, ty)) ctrs' vs
             else begin
                 let up   = try Some (convert_up true 0 ctr ty ctr' ty' vs [])
                            with ConversionError -> None in
                 let down = try Some (convert_down    0 ctr ty ctr' ty' vs [])
                            with ConversionError -> None in
                 catMaybes [up ; down] @ convert_ctr ((ctr,ty)) ctrs' vs
               end 
          | [] -> []
        in

      let create_branch aux_fuzz (ctr, ty) =
        (ctr, generate_names_from_type "p" ty,
         fun all_vars ->
         (* Fuzz options based on the different constructors *)
         let opts_base = convert_ctr (ctr, ty) ctrs all_vars in

         let rec aux opts ty acc_vars : coq_expr =
           match ty, acc_vars with
           | Arrow (ty1, ty2), v :: vs ->
              (* lift a generator for ty1 to a generator for the whole thing *)
              let liftNth g =
                bindGen g "fuzzed" (fun fuzzed ->
                    returnGen (gApp ~explicit:true (gCtr ctr)
                                               (tyParams @ (replace (gVar v) (gVar fuzzed) (List.map gVar all_vars))))) in
              let fuzz_options = 
                if isCurrentTyCtr ty1 then
                  (* Recursive argument. Fuzz with aux, or keep *)
                  [ liftNth (gApp (gVar aux_fuzz) [gVar v])
                  ; returnGen (gVar v)
                  ]
                else
                  [ liftNth (gApp (gInject "fuzz") [gVar v]) ]
              in 

              aux (fuzz_options @ opts) ty2  vs
           (* Finalize, pick one of the options, using oneof' for now. *)
           | _ ->
              (* If no options are available (i.e, you're fuzzing a nullary constructor,
                 just generate an arbitrary thing *)
              begin match opts with
              | [] -> gInject "arbitrary"
              | _  -> oneof' (List.map (fun x -> (gFunTyped [("_tt", gUnit)] (fun _ -> x))) opts)
              end
         in aux opts_base ty all_vars)
      in

      let aux_fuzz_body rec_fun x' = gMatch (gVar x') (List.map (create_branch rec_fun) ctrs) in

      gRecFunIn "aux_fuzz" ["x'"]
        (fun (aux_fuzz, [x']) -> aux_fuzz_body aux_fuzz x')
        (fun aux_fuzz -> gApp (gVar aux_fuzz) [gVar x])
    in
    (* Create the function body by recursing on the structure of x *)
    gFun ["x"] (fun [x] -> fuzzy_body x)
  in
  debug_coq_expr fuzzy_fun;
  gRecord [("fuzz", fuzzy_fun)]


(** Shrinking Derivation *)
let shrink_decl ty_ctr ctrs iargs =

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  let tyParams = List.map gVar (list_drop_every 2 iargs) in

  let shrink_fun = 
    let shrink_body x =
      let create_branch aux_shrink (ctr, ty) =
        (ctr, generate_names_from_type "p" ty,
         fold_ty_vars (fun allParams v ty' ->
             let liftNth = gFun ["shrunk"]
                 (fun [shrunk] -> gApp ~explicit:true (gCtr ctr)
                     (tyParams @ (replace (gVar v) (gVar shrunk) (List.map gVar allParams)))) in
             lst_appends (if isCurrentTyCtr ty' then
                            [ gList [gVar v] ; gApp (gInject "List.map") [liftNth; gApp (gVar aux_shrink) [gVar v]]]
                          else
                            [ gApp (gInject "List.map") [liftNth; gApp (gInject "shrink") [gVar v]]]))
           lst_append list_nil ty) in

      let aux_shrink_body rec_fun x' = gMatch (gVar x') (List.map (create_branch rec_fun) ctrs) in

      gRecFunIn "aux_shrink" ["x'"]
        (fun (aux_shrink, [x']) -> aux_shrink_body aux_shrink x')
        (fun aux_shrink -> gApp (gVar aux_shrink) [gVar x])
    in
    (* Create the function body by recursing on the structure of x *)
    gFun ["x"] (fun [x] -> shrink_body x)
  in
  debug_coq_expr shrink_fun;
  gRecord [("shrink", shrink_fun)]

let show_decl ty_ctr ctrs iargs =
  msg_debug (str "Deriving Show Information:" ++ fnl ());
  msg_debug (str ("Type constructor is: " ^ ty_ctr_to_string ty_ctr) ++ fnl ());
  msg_debug (str (str_lst_to_string "\n" (List.map ctr_rep_to_string ctrs)) ++ fnl());

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  (* Create the function body by recursing on the structure of x *)
  let show_body x =
    
    let branch aux (ctr,ty) =
      
      (ctr, generate_names_from_type "p" ty,
       fun vs -> match vs with 
                 | [] -> gStr (constructor_to_string ctr) 
                 |_ -> str_append (gStr (constructor_to_string ctr ^ " "))
                                  (fold_ty_vars (fun _ v ty' -> smart_paren (gApp (if isCurrentTyCtr ty' then gVar aux else gInject "show") [gVar v]))
                                                (fun s1 s2 -> if s2 = emptyString then s1 else str_appends [s1; gStr " "; s2]) emptyString ty vs))
    in
    
    gRecFunIn "aux" ["x'"]
              (fun (aux, [x']) -> gMatch (gVar x') (List.map (branch aux) ctrs))
              (fun aux -> gApp (gVar aux) [gVar x])
  in
  
  let show_fun = gFun ["x"] (fun [x] -> show_body x) in
  gRecord [("show", show_fun)]
          
