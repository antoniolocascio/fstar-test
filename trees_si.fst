module Trees_si
open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Math.Lemmas
module Integers = FStar.Integers
module Int = FStar.Int
module Int64 = FStar.Int64
module Seq = FStar.Seq.Base

assume type byte:eqtype
assume val hash_size:nat

type hash = b:Seq.seq byte{Seq.length b == hash_size}
type commitment = hash

let int64 = Int64.t

(** Incremental Merkle Tree
     *
     * A tree of height h contains 2^h leaves and h+1 levels of nodes with
     * leaves at level 0 and root at level h.
     *
     * The leaves are commitments and the tree is treated as always filled
     * with a default value H.uncommitted. This allows to have proofs of
     * membership, or witnesses, of fixed size.
     *
     * All the nodes at the same level of an empty tree have the same hash,
     * which can be computed from the default value of the leaves. This is
     * stored in the [uncommitted] list.
     *
     * Any subtree filled with default values is represented by the Empty
     * constructor and given its height it's possible to compute its hash
     * using the [uncommitted] list.
     *
     * The leaves are indexed by their position [pos], ranging from 0 to
     * (2^h)-1. The encoding of [pos] limits the possible size of the tree.
     * In any case the only valid height for the Sapling library is 32, so even
     * if the library encodes positions as uint64, they never exceed uint32.
     *
     * The tree is incremental in the sense that leaves cannot be modified but
     * only added and exclusively in successive positions.
     * The type t contains the size of the tree which is also the next position
     * to fill.
     *
     * Given that elements are added and retrieved by position, it is possible
     * to use this information to efficiently navigate the tree.
     * Given a tree of height [h] and a position [pos], if pos < pow2 (h-1) only
     * the left subtree needs to be inspected recursively. Otherwise only the
     * right needs to be visited, decreasing [pos] by [pow2 (h-1)].
     *
     * In order to avoid storing the height for each subtree (or worse
     * recomputing it), each function with suffix `_height` expects the height
     * of the tree as parameter. These functions are only for internal use and
     * are later aliased by functions using the default height of a Sapling
     * incremental Merkle tree.
 *)

type tree = 
  | Empty : tree
  | Leaf : commitment -> tree
  | Node : h:hash -> l:tree -> r:tree -> tree

type list64 a = l:list a{Int.fits (length l) 64 }

type nat64 = n:int64{Integers.(n >= 0L)}

val length64 : l:list64 'a -> Tot (n:nat64)
let length64 l = Int64.int_to_t (List.Tot.Base.length l)

assume val hashT : nat64 -> tree -> tree -> hash


(*
  [split_at n l1] splits the list [l1] into two lists, the first of which is
  at most of length n.
*)

val split_at : n:nat64 -> l1:list64 'a
  -> Pure (list64 'a * list64 'a)
         (requires true)
         (ensures (fun(l2, l3) -> Integers.((length64 l2 <= n)
                               /\ (length64 l3 == 0L \/ length64 l3 == length64 l1 - n)
                               /\ length64 l2 + length64 l3 == length64 l1
                               /\ l1 == l2 @ l3)))
         (decreases l1)      
let rec split_at n l =
  let open Integers in
  if n = 0L then ([], l)
  else
    match l with
    | [] -> ([], l)
    | x :: xs ->
       let (l1, l2) = split_at (n - 1L) xs in
       (x :: l1, l2)

(* 
  [sizeT t] computes the actual size of the tree [t].
*)
val sizeT : tree -> Tot nat
let rec sizeT t =
  match t with 
  | Empty -> 0
  | Leaf _ -> 1
  | Node _ l r -> sizeT l + sizeT r

(* 
  [heightT t] computes the actual height of the tree [t].
*)
val heightT : t:tree -> Tot nat
let rec heightT t = 
  match t with 
  | Empty -> 0
  | Leaf _ -> 0
  | Node _ l r -> 
    let (hl, hr) = (heightT l, heightT r) in
    if hl > hr then 1 + hl else 1 + hr


type tree64 = t:tree{Int.fits (sizeT t) 64 /\ Int.fits (heightT t) 64}

val sizeT64 : t:tree64 -> Tot (n:nat64{Int64.v n == sizeT t})
let rec sizeT64 t =
  match t with 
  | Empty -> 0L
  | Leaf _ -> 1L
  | Node _ l r -> Integers.((sizeT64 l) + (sizeT64 r))

val heightT64 : t:tree64 -> Tot (h:nat64{Int64.v h == heightT t})
let rec heightT64 t = 
  match t with 
  | Empty -> 0L
  | Leaf _ -> 0L
  | Node _ l r -> 
    let (hl, hr) = (heightT64 l, heightT64 r) in
    Integers.(if hl > hr then 1L + hl else 1L + hr)

val pow2_64 : e:nat64{Integers.(e <= 32L)} -> Tot int64
let pow2_64 e = 
  let ue = UInt.to_uint_t 32 (Int64.v e) in
  Int64.shift_left 1L (UInt32.uint_to_t ue)
 

val pow2_correct : e:nat64{Integers.(e <= 32L)}  -> Lemma 
  (ensures ((Int64.v (pow2_64 e)) == pow2 (Int64.v e)))
  [SMTPat (pow2_64 e)]
let pow2_correct e = 
    let e' = (UInt32.uint_to_t (UInt.to_uint_t 32 (Int64.v e))) in
    Int.shift_left_value_lemma #64 1 (Int64.v e);
    pow2_le_compat 32 (Int64.v e)
    // s=(UInt32.uint_to_t (UInt.to_uint_t 32 (Int64.v e)))
    
    // Int64.v (Int64.shift_left 1L s)
    //={Int64.shift_left post condition}
    // Int.shift_left (Int64.v 1L) (UInt32.v s)
    //={Int.shift_left_value_lemma}
    // ((Int64.v 1L) * pow2 (UInt32.v s)) @% pow2 64
    //={1 ne of *}
    // pow2 (UInt32.v s) @% pow2 64
    //={pow2_le_compat...}
    // pow2 (UInt32.v s)
    //={conversions}
    // pow2 (Int64.v e)


(*
  Lemma: the size of a tree [t] of height of at most [h] is bound by 2^h.
*)
val size_height_lemma : t:tree -> h:nat
  -> Lemma (requires h >= heightT t)
          (ensures sizeT t <= pow2 h)
let rec size_height_lemma t h = 
  match t with 
  | Empty -> ()
  | Leaf _ -> ()
  | Node _ l r -> 
    let (hl, hr) = (heightT l, heightT r) in
    assert (hl <= h - 1);
    assert (hr <= h - 1);
    size_height_lemma l hl; 
    size_height_lemma r hr;
    pow2_le_compat (h - 1) hl;
    pow2_le_compat (h - 1) hr;
    pow2_double_sum (h - 1)


(*
  [full t h] determines if the tree [t] of height [h] is full.
  Note: [h] might not be [t]'s actual height, due to the representation of 
  subtrees filled with default values.
*)
val full : t:tree -> h:nat -> Tot bool
let rec full t h = 
  match t,h with 
  | Empty, 0 -> false  
  | Leaf _, 0 -> true
  | _ , 0 -> false
  | Node _ l r , _ -> full l (h - 1) && full r (h - 1)
  | _ , _ -> false   

(*
  Lemma: If (Node _ l r) is full, then both l and r are full.
*) 
val full_hereditary_lemma : t:tree -> h:nat 
  -> Lemma (requires (full t h /\ Node? t))
          (ensures (  full (Node?.l t) (h - 1) 
                    /\ full (Node?.r t) (h - 1)))
          [SMTPat (full t h)]
let full_hereditary_lemma t h  = ()

(*
  Lemma: A tree of height h is full iff its size is 2^h.
*)
val size_full_lemma : t:tree -> h:nat{h >= heightT t}
  -> Lemma (requires (True))
          (ensures ((sizeT t = pow2 h) = (full t h)))
let rec size_full_lemma t h = 
  match t,h with 
  | Empty, 0 -> ()
  | Leaf _, 0 -> ()
  | _, 0 -> ()
  | Node _ l r, _ -> 
    size_full_lemma l (h - 1);
    size_full_lemma r (h - 1);
    size_height_lemma l (h - 1);
    size_height_lemma r (h - 1)
  | _, _ -> ()

(*
  A tree [t] of height [h] is incremental if all of its leaves are on the left in
  successive postions.
  TODO: Is this enough?
*)
val incremental : t:tree -> h:nat -> Tot bool
let rec incremental t h =
  h >= heightT t && 
  (match t with 
  | Leaf _ -> h = 0 
  | Empty -> true
  | Node _ l r -> 
    if full l (h - 1) then incremental r (h - 1)
    else sizeT r = 0 && incremental l (h - 1))

(*
  Lemma: every full tree is incremental.
*)
val full_incremental_lemma : t:tree -> h:nat{h >= heightT t}
  -> Lemma (requires (full t h))
          (ensures (incremental t h))
          [SMTPat (full t h)]
let rec full_incremental_lemma t h = 
  match t with 
  | Empty -> ()
  | Leaf _ -> ()
  | Node _ l r -> full_incremental_lemma r (h - 1)

(*
  Lemma: every empty tree is incremental.
*)
val empty_incremental_lemma : t:tree -> h:nat{h >= heightT t}
  -> Lemma (requires (sizeT t == 0))
          (ensures (incremental t h))
let rec empty_incremental_lemma t h = 
  match t with 
  | Empty -> ()
  | Node _ l r -> 
    empty_incremental_lemma l (h - 1);
    empty_incremental_lemma r (h - 1)

(*
  Lemma: If (Node _ l r) is incremental, then both l and r are incremental.
*)
val incremental_hereditary : t:tree -> h:nat{h >= heightT t}
  -> Lemma (requires (incremental t h /\ Node? t))
          (ensures (  incremental (Node?.l t) (h - 1) 
                    /\ incremental (Node?.r t) (h - 1)))
          [SMTPat (incremental t h)]
let rec incremental_hereditary t h  = 
  match t with 
  | Empty -> ()
  | Leaf _ -> ()
  | Node _ l r -> 
    if full l (h - 1) then () 
    else empty_incremental_lemma r (h - 1)

(*
  Lemma: If (Node _ l r) is incremental and l is not full,
         then r is empty.
*)
val incremental_lemma1 : t:tree -> h:nat{h >= heightT t}
  -> Lemma (requires (incremental t h /\ Node? t))
          (ensures (sizeT t < pow2 (h - 1) ==> sizeT (Node?.r t) == 0))
let incremental_lemma1 t h = 
  match t with 
  | Node _ l t -> 
    size_full_lemma l (h - 1)

(*
  Lemma: If (Node _ l r) is incremnetal of height h and its size is > 2^(h-1),
         then l is full.
*)
val incremental_lemma2 : t:tree -> h:nat{h >= heightT t}
  -> Lemma (requires (incremental t h /\ Node? t))
          (ensures (sizeT t >= pow2 (h - 1) ==> sizeT (Node?.l t) == pow2 (h - 1)))
let incremental_lemma2 t h = 
  match t with 
  | Node _ l r -> 
    if full l (h - 1) 
    then size_full_lemma l (h - 1) 
    else size_height_lemma l (h - 1)

val incremental_lemma3 : t1:tree -> t2:tree -> h:nat{h >= heightT t1 /\ h >= heightT t2}
  -> Lemma (requires (  incremental t1 h
                     /\ incremental t2 h
                     /\ (~ (full t1 h) ==> sizeT t2 == 0 )))
          (ensures (forall c . incremental (Node c t1 t2) (h + 1)))
let incremental_lemma3 t1 t2 h = ()

(*
  [to_list t] returns the list of elements present in the tree [t].
*)
val to_list : t:tree -> list commitment
let rec to_list t = 
  match t with
  | Empty -> []
  | Leaf x -> [x]
  | Node _ l r -> to_list l @ to_list r

(*
  Lemma: The size of a tree is equal to the length of the list of its elements.
*)
val list_length_size_lemma : t:tree 
  -> Lemma (requires True)
          (ensures (sizeT t == length (to_list t)))
let rec list_length_size_lemma t = 
  match t with
  | Empty -> ()
  | Leaf _ -> ()
  | Node _ l r -> 
    list_length_size_lemma l;
    list_length_size_lemma r


(*
  [insert tree height pos cms] inserts the list of commitments
  [cms] in the tree [tree] of height [height] at the next position [pos].
  Pre: incremental tree /\
       size tree + List.length cms <= pow2 height /\
       pos = size tree /\
  Post: incremental tree /\
        to_list (insert tree height pos cms) = to_list t @ cms
*)

val insert : t:tree64
           -> height:nat64{(Int64.v height) <= 32 /\ (Int64.v height) >= heightT t}
           -> pos:nat64{Int64.v pos < pow2 (Int64.v height) /\ Int64.v pos == sizeT t} 
           -> cms:list64 commitment {length cms + sizeT t <= pow2 (Int64.v height)}
           -> Pure tree
                 (requires (incremental t (Int64.v height)))
                 (ensures (fun t' ->   incremental t' (Int64.v height)
                                  /\ to_list t' == to_list t @ cms))
                 (decreases %[Int64.v height;0])

val insert_node : t1:tree
                -> t2:tree 
                -> height:nat64{  Int64.v height <= 32 
                               /\ Int64.v height >= heightT t1 
                               /\ Int64.v height >= heightT t2}
                -> pos:nat64{  Int64.v pos < pow2 (Int64.v height + 1) 
                            /\ Int64.v pos == sizeT t1 + sizeT t2} 
                -> cms:list64 commitment{length cms + Int64.v pos <= 
                                             pow2 (Int64.v height + 1)}
                -> Pure tree 
                      (requires (  incremental t1 (Int64.v height)
                                 /\ incremental t2 (Int64.v height)
                                 /\ (Int64.v pos < pow2 (Int64.v height) 
                                     ==> sizeT t2 == 0)
                                 /\ (Int64.v pos >= pow2 (Int64.v height)
                                     ==> sizeT t1 == pow2 (Int64.v height))))
                      (ensures (fun t' ->   incremental t' ((Int64.v height) + 1)
                                       /\ to_list t' == to_list t1 @ to_list t2 @ cms))
                      (decreases %[Int64.v height;1])
 
#set-options "--z3rlimit 30"

let rec insert tree height pos cms = 
  //assert (pos >= 0 && pos <= pow2 height);
  //assert (height >= 0 && height <= 32);
  match (tree, height, cms) with
  | (_, _, []) ->
      tree
  | (Empty, 0L, [cm]) ->
      Leaf cm
  // The following two cases aren't needed.
  (*| (Leaf _, _, _) -> 
    admit()*)
  (* The second conjuntion of the precondition is violated by a Leaf (which
     is already full) and a non empty cms. *)
  (*| (_, 0, _) ->
      (* Only leaves can be at height 0. *)
      admit() *)
  | (Empty, height, _) ->
      insert_node Empty Empty Integers.(height - 1L) pos cms
  | (Node _ t1 t2, height, _) ->
      incremental_lemma1 tree (Int64.v height);
      incremental_lemma2 tree (Int64.v height);
      append_assoc (to_list t1) (to_list t2) cms;
      insert_node t1 t2 Integers.(height - 1L) pos cms 
      
and insert_node t1 t2 height posi cms =
  let (t1', t2') =
    let open Integers in
    if posi < pow2_64 height then (
      let at =  (pow2_64 height) -  posi in
      let (cml, cmr) = split_at at cms in
      let t1' = insert t1 height posi cml in
      list_length_size_lemma t1';
      list_length_size_lemma t1;
      size_full_lemma t1' (Int64.v height);
      let t2' = insert t2 height 0L cmr in
      list_length_size_lemma t2';
      list_length_size_lemma t2;
      size_height_lemma t1' (Int64.v height);
      incremental_lemma3 t1' t2' (Int64.v height); 
      append_assoc (to_list t1) cml cmr;
      append_nil_l cms;
      (t1', t2') )
    else 
      (
      let pos' = ( posi - (pow2_64 height)) in
      let t2' = insert t2 height pos' cms in
      size_full_lemma t1 (Int64.v height);
      (t1, t2') 
      )
  in
  let h = hashT height t1' t2' in 
  Node h t1' t2'
