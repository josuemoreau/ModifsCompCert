(** Coalescing *)
open Camlcoq
open Maps
open SSA
open SSAutils

module PosSet = Set.Make(struct
  type t = SSA.node
  let compare = compare
end)

let set_from_list l =
  List.fold_left (fun set elt -> PosSet.add elt set) PosSet.empty l

let regset_from_list l =
  List.fold_left (fun set elt -> SSARegSet.add elt set) SSARegSet.empty l

(** debug utilities *)
let diag m =
  Printf.printf "%s\n" m;
  flush_all()

let dump_reg r =
  Printf.printf "x%ld" (P.to_int32 r)

let dump_node pc =
  Printf.printf "pc_%ld" (P.to_int32 pc)

(** compute cssa value *)
let compute_cssaval_function (f : CSSApar.coq_function) =
  let cssaval_hash = Hashtbl.create 16 in  
  let get_cssaval r =
    try Hashtbl.find cssaval_hash r with
    Not_found -> r
  in

  (* depth first search *)
  let sorted_nodes = Stack.create () in
  let unvisited =
    ref (set_from_list (List.rev_map fst (PTree.elements f.CSSApar.fn_code))) in
  let rec visit pc =
    if not (PosSet.mem pc !unvisited) then ()
    else begin
      unvisited := PosSet.remove pc !unvisited;
      match PTree.get pc f.CSSApar.fn_code with
      | None     -> assert false
      | Some ins ->
          List.iter visit (successors_instr ins);
          Stack.push pc sorted_nodes
    end
  in
  visit f.CSSApar.fn_entrypoint;
  if not (PosSet.is_empty !unvisited) then
    diag "Warning: some not accessible nodes";

  (* node processing *)
  let rec do_node pc =
    match PTree.get pc f.CSSApar.fn_code with
    | None     -> assert false
    | Some ins ->
        begin
          if PTree.get pc f.CSSApar.fn_phicode <> None then
            match PTree.get pc f.CSSApar.fn_parcopycode with
            | None       -> assert false
            | Some parcb ->
                do_parcopyblock parcb;
                do_instruction ins
          else
            do_instruction ins;
            match PTree.get pc f.CSSApar.fn_parcopycode with
            | None       -> ()
            | Some parcb -> do_parcopyblock parcb
        end
  and do_instruction ins = match ins with
    | Iop(Op.Omove, src :: nil, dst, _) ->
        Hashtbl.add cssaval_hash dst (get_cssaval src)
    | _ -> ()
  and do_parcopyblock parcb =
    List.iter
      (function CSSApar.Iparcopy(src, dst) ->
        Hashtbl.add cssaval_hash dst (get_cssaval src))
      parcb
  in
  while not (Stack.is_empty sorted_nodes) do
    do_node (Stack.pop sorted_nodes)
  done;

  (* return cssaval function *)
  get_cssaval

(** initialize classes with phi variables *)
let initialize_classes f =
  let repr_hash = Hashtbl.create 16 in
  let classes =
    PTree.fold
      (fun acc pc phib ->
        List.fold_left
          (fun acc (Iphi(args,dst)) ->
            PTree.set dst
              (List.fold_left
                (fun cls r ->
                  Hashtbl.add repr_hash r dst;
                  r :: cls)
                []
                (dst :: args))
              acc)
          acc
          phib)
      f.CSSApar.fn_phicode
      PTree.empty in
  (classes, repr_hash)

let get_class repr classes =
  match PTree.get repr classes with
  | Some cls -> cls
  | None -> []

(** build coalescing classes of non interfering variables *)
let build_coalescing_classes_extern f ninterfere =
  let (classes, repr_hash) = initialize_classes f in
  let regrepr r =
    try Hashtbl.find repr_hash r
    with Not_found -> r
  in
  let classes = PTree.fold
    (fun acc pc parcb ->
      match PTree.get pc f.CSSApar.fn_phicode with
      | Some phib ->
          List.fold_left
            (fun acc (CSSApar.Iparcopy(repr,dst)) ->
              let repr_class = get_class repr acc in
              let dst_class = 
                match get_class (regrepr dst) acc with
                | [] -> [dst]
                | l -> l 
              in
              if List.for_all
                  (fun r ->
                     List.length dst_class < 1000 &&
                     List.for_all
                      (fun r' -> ninterfere r' r)
                      dst_class)
                  repr_class
              then begin
                List.iter
                  (fun r -> Hashtbl.add repr_hash r repr)
                  dst_class;
                PTree.set repr (List.rev_append dst_class repr_class) acc
              end
              else acc)
            acc
            parcb
      | None -> acc)
    f.CSSApar.fn_parcopycode
    classes
  in
  let classes = PTree.fold
    (fun acc pc parcb ->
      match PTree.get pc f.CSSApar.fn_phicode with
      | Some phib -> acc
      | None ->
          List.fold_left
            (fun acc (CSSApar.Iparcopy(src,dst)) ->
              let repr = Hashtbl.find repr_hash dst in
              let dst_class = get_class repr acc in
              let src_class = 
                match get_class (regrepr src) acc with
                | [] -> [src]
                | l -> l 
              in
              if List.for_all
                  (fun r ->
                    List.length src_class < 1000 &&
                    List.for_all
                      (fun r' -> ninterfere r' r)
                      src_class)
                  dst_class
              then begin
                List.iter
                  (fun r -> Hashtbl.add repr_hash r repr)
                  src_class;
                PTree.set repr (List.rev_append src_class dst_class) acc
              end
              else acc)
            acc
            parcb)
    f.CSSApar.fn_parcopycode
    classes
  in
  (regrepr, classes)

(* (* simple version *)
let build_coalescing_classes_extern f ninterfere =
  let (classes, repr_hash) = initialize_classes f in
  let classes = PTree.fold
    (fun acc pc parcb ->
      match PTree.get pc f.fn_phicode with
      | Some phib ->
          List.fold_left
            (fun acc (Iparcopy(repr,dst)) ->
              let repr_class = Utils.P2Map.get repr acc in
              if List.for_all
                  (fun r -> ninterfere dst r)
                  repr_class
              then begin
                Hashtbl.add repr_hash dst repr;
                Utils.P2Map.set repr (dst :: repr_class) acc
              end
              else acc)
            acc
            parcb
      | None -> acc)
    f.fn_parcopycode
    classes
  in
  let _ (* classes *) = PTree.fold
    (fun acc pc parcb ->
      match PTree.get pc f.fn_phicode with
      | Some phib -> acc
      | None ->
          List.fold_left
            (fun acc (Iparcopy(src,dst)) ->
              let repr = Hashtbl.find repr_hash dst in
              let dst_class = Utils.P2Map.get repr acc in
              if List.for_all
                  (fun r -> ninterfere src r)
                  dst_class
              then begin
                Hashtbl.add repr_hash src repr;
                Utils.P2Map.set repr (src :: dst_class) acc
              end
              else acc)
            acc
            parcb)
    f.fn_parcopycode
    classes
  in
  let regrepr r =
    try Hashtbl.find repr_hash r
    with Not_found -> r
  in
  (* (* XXX : perhaps usefull for a check *)
  let regclass r =
    Utils.P2Map.get r classes
  in *)
  regrepr
*)
