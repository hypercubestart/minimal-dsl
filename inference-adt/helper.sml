(*helper functions since sml :( *)
use "ast.sml";

structure T = Types;

structure Helper =
struct
  fun removeIfContains(ht, key) = 
    if contains(ht, key) then (HashTable.remove ht key; ()) else ()

  and contains(ht, key) = (case HashTable.find ht key of
     SOME(_) => true
   | NONE => false)
  
  (* t = App(TyFun(...)) *)
  fun meta1(t) = case t of
     T.App(T.TyFun(_, _), _) => true
   | _ => false

  (* ty = Meta(y) and y in ht *)
  fun meta2(ht, ty) = case ty of
     T.Meta(meta) => contains(ht, meta)
   | _ => false

  (* ty = Meta(meta) *)
  fun meta3(meta, ty) = case ty of
    T.Meta(b) => meta = b
    | _ => false

end