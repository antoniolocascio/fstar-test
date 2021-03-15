module Roots
open FStar.Math.Lemmas
open FStar.List.Tot
open FStar.List.Tot.Properties
//module Int32 = FStar.Int32
open FStar.Int 

module Map = FStar.Map
module S = FStar.Set

type hash = int

let default_hash = 0

let size = 500

type position = pos:nat{pos < size}

type t = (pos : position) * (m:(Map.t position hash))

let empty : t = (0, Map.const_on Set.empty default_hash)


val add : e:hash -> p:t 
  -> Pure t
    (requires true)
    (ensures (fun (pos', map') -> 
              let (pos, map) = p in 
              pos' == pos
              /\ map' == Map.upd map pos e
              ))

let add e ((pos, map)) =
  let map' = Map.upd map pos e in
  let pos' = mod #32 pos size in
  (pos', map')



(* let mem e ((_, map) : t) =
  Map.exists (fun _ v -> Compare.Int.(C.Hash.compare e v = 0)) map

let to_list ((_, m) : t) = List.map snd (Map.bindings m)

let of_list = List.fold_left (fun m e -> add e m) empty
*)
