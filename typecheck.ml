open Syntax

type context = (TermVar.t , Typ.t) Hashtbl.t

let rec typecheck (ctx : context) (t : Term.t) : (Typ.t * context) option =
  match Term.out t with
    (* IDENTITY RULE *)
    | Term.Var x -> (try
                      (let tp = Hashtbl.find ctx x in
                       let () = Hashtbl.remove ctx x in
                          Some (tp , ctx)) with
                    | _ -> None)
    (* Lollipop Right *)
    | Term.Lam ((x , tp) , t') -> let () = Hashtbl.add ctx x tp in
                                  let stp = typecheck ctx t' in
                                    (match stp with
                                      | None -> None
                                      | Some (tp' , rest_ctx) -> Some (Typ.Lolli (tp , tp') , rest_ctx))
    (* Tensor Right *)
    | Term.TenPair (t1 , t2) -> let stp = typecheck ctx t1 in
                                (match stp with
                                    | None -> None
                                    | Some (tp1 , rest_ctx) ->
                                    (match typecheck rest_ctx t2 with
                                        | None -> None
                                        | Some (tp2 , rest_ctx2) -> Some (Typ.Tensor (tp1,tp2) , rest_ctx2)))
    (* With Right *)
    | Term.WithPair (t1 , t2) -> (match (typecheck ctx t1 , typecheck ctx t2) with
                                  | (Some (tp1 , rest1) , Some (tp2 , rest2)) -> Some (Typ.With (tp1 , tp2) , rest2)
                                  | _ -> None)
    (* Or Right 1 *)
    | Term.Inl (tp , t') -> (match typecheck ctx t' with
                          | Some (tp' , rest) -> Some (Typ.Or (tp' , tp), rest)
                          | None -> None)
    (* Or Right 2 *)
    | Term.Inr (tp , t') -> (match typecheck ctx t' with
                          | Some (tp' , rest) -> Some (Typ.Or (tp , tp'), rest)
                          | None -> None)
    (* Top right *)
    | Term.Unit -> Some (Typ.Top , ctx)
    (* 1 Right *)
    | Term.Star -> Some (Typ.One , ctx)
    (* Or Left *)
    | Term.Case (zt , (x , u) , (y , v)) ->
        (match Term.out zt with
          | Term.Var z ->
                                        (try (let a_plus_b = Hashtbl.find ctx z in
                                                match a_plus_b with
                                                | Typ.With (a , b) ->
                                                  ( let () = Hashtbl.remove ctx z in
                                                    let () = Hashtbl.add ctx x a in
                                                    match typecheck ctx u with
                                                    | None -> None
                                                    | Some (c , rest_ctx) ->
                                                    let () = Hashtbl.remove ctx x in
                                                    let () = Hashtbl.add ctx y b in
                                                    match typecheck ctx v with
                                                    | None -> None
                                                    | Some (c', rest_ctx2) ->
                                                    if Typ.aequiv c c' then Some (c' , rest_ctx2)
                                                    else None
                                                    )
                                                | _ -> None
                                                ) with
                                           | _ -> None)
          | _ -> None)
    | Term.Let (tm , zt , tm') ->
        (match Term.out zt with
        | Term.Var z ->
                                (* Cut *)
                                (try (match typecheck ctx tm with
                                      | None -> failwith "not a cut"
                                      | Some (tp , rest) ->
                                            let () = Hashtbl.add rest z tp in
                                            (match typecheck rest tm' with
                                            | None -> failwith "not a cut"
                                            | Some c -> Some c)
                                        )
                                 with
                                 | _ ->
                                (* Lolli Left *)
                                (try (match Term.out tm with
                                     | Term.App (ft , t) -> (match Term.out ft with
                                       | Term.Var f -> (try ( let tp = Hashtbl.find ctx f in
                                                               (match tp with
                                                                 | Typ.Lolli (a , b) ->
                                                                   let () = Hashtbl.remove ctx f in
                                                                   (match typecheck ctx t with
                                                                     | Some (a' , rest) when Typ.aequiv a a' ->
                                                                       let () = Hashtbl.add rest z b in
                                                                         typecheck rest tm'
                                                                     | _ -> failwith "not an app")
                                                                 | _ -> failwith "not an app"))
                                                        with
                                                       | _ -> failwith "not an app" )
                                       | _ -> failwith "not an app" )
                                     | _ -> failwith "not an app")
                                with
                                | _ ->
                                (try (let tp = Hashtbl.find ctx z in
                                      match (Term.out tm , tp) with
                                      (* 1 Left*)
                                      | (Term.Unit , Typ.One) ->
                                        let () = Hashtbl.remove ctx z in
                                          typecheck ctx tm'
                                      (* Tensor Left *)
                                      | (Term.TenPair (xt , yt) , Typ.Tensor(a , b)) ->
                                        (match (Term.out xt,Term.out yt) with
                                          | (Term.Var x , Term.Var y) ->
                                            let () = Hashtbl.remove ctx z in
                                            let () = Hashtbl.add ctx x a in
                                            let () = Hashtbl.add ctx y b in
                                              typecheck ctx tm'
                                          | _ -> None)
                                      (* With Left 1*)
                                      | (Term.WithPair (xt , yt) , Typ.With (a , b)) ->
                                        (match (Term.out xt , Term.out yt) with
                                          | (Term.Var x , ytp) ->
                                            let () = Hashtbl.remove ctx z in
                                            let () = Hashtbl.add ctx x a in
                                              (match typecheck ctx tm' with
                                                | Some res -> Some res
                                                | None ->
                                                (match ytp with
                                                  | Term.Var y ->
                                                    let () = Hashtbl.remove ctx x in
                                                    let () = Hashtbl.add ctx y b in
                                                      typecheck ctx tm'
                                                  | _ -> None))
                                          (* With Left 2*)
                                          | (_ , Term.Var y) ->
                                            let () = Hashtbl.remove ctx z in
                                            let () = Hashtbl.add ctx y b in
                                              typecheck ctx tm'
                                          | _ -> None)
                                      | _ -> None
                                      ) with
                                  | _ -> None)
                                  ))
         | _ -> None)
    | _ -> None

let typechecker ctx t =
  match typecheck ctx t with
    | Some (tp , rest_ctx) -> if Hashtbl.length rest_ctx = 0 then tp else failwith "cannot typecheck"
    | _ -> failwith "cannot typecheck"
