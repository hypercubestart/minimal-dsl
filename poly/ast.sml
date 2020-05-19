(* SYMBOL TABLE *)
signature SYMBOL =
sig
  eqtype symbol
  val symbol : string -> symbol
  val name : symbol -> string

  type 'a table
  val empty : 'a table
  val enter : 'a table * symbol * 'a -> 'a table
  val look : 'a table * symbol -> 'a option
end

structure Symbol :> SYMBOL = 
struct
    type symbol = string * int

    exception Symbol
    val nextsym = ref 0
    val hashtable : (string, int) HashTable.hash_table = 
        HashTable.mkTable(HashString.hashString, op = ) (128,Symbol)

    fun symbol name = 
        case HashTable.find hashtable name
            of SOME i => (name, i)
            |  NONE => let val i = !nextsym
                        in nextsym := i + 1;
                           HashTable.insert hashtable (name,i);
                           (name,i)
                        end

    fun name(s,n) = s

    type 'a table = 'a IntBinaryMap.map
    val empty = IntBinaryMap.empty
    fun enter(t: 'a table, (s,n): symbol, a: 'a) = IntBinaryMap.insert(t,n,a)
    fun look(t: 'a table, (s,n): symbol) = IntBinaryMap.find(t,n)                   
end
(* --------------AST--------------- *)
structure AbSyntax =
struct
type symbol = Symbol.symbol

datatype var = SimpleVar of symbol
            |  FieldVar of var * symbol

and exp = 
    VarExp of var
|   NilExp
|   IntExp of int
|   StringExp of string
|   CallExp of {func: symbol, tyargs: ty list, arg: exp}
|   OpExp of {left: exp, oper: oper, right: exp}
|   RecordExp of {typ: symbol, tyargs: tyargs, fields: (symbol * exp) list}
|   SeqExp of exp list
|   AssignExp of {var: var, exp: exp}
|   LetExp of {decs: dec list, body: exp}

and dec = 
    FunctionDec of fundec list
|   VarDec of {name: symbol, typ: symbol, init: exp}
|   TypeDec of tydec list

and ty = NameTy of symbol
|    RecordTy of tyfields
|    PolyTy of tyvars * ty
|    TyCon of symbol * tyargs
and tydec = ParametricTyc of symbol * tyvars * ty
|   RecordTyDec of symbol * tyvars * tyfields

and oper = PlusOp | MinusOp
withtype tyfields = (symbol * ty) list
and tyvars = symbol list
and tyargs = ty list
and fundec = {name: symbol, tyvars: tyvars, param: symbol, result: symbol, body: exp}
end

(* Types *)
structure Types =
struct
  type unique = unit ref

  datatype ty = Nil
            |   App of tycon * ty list
            |   Var of tyvar
            |   Poly of tyvar list * ty
    and tycon = Int | String | Unit | Arrow
            |   Record of AbSyntax.symbol list
            |   TyFun of tyvar list * ty
            |   Unique of tycon * unique
    withtype tyvar = int
end

(* Environment *)
signature ENV =
sig
  (* type access *)
  (* type ty *)
  datatype enventry = VarEntry of {ty:Types.ty}
                    | FunEntry of {ty: Types.ty}
  datatype tenventry = TyEntry of {ty: Types.ty}
                    |  TyConEntry of {tycon: Types.tycon}
  val base_tenv : tenventry Symbol.table (*predefined types*)
  val base_venv : enventry Symbol.table (*predefined functions*)
end

structure Env :> ENV =
struct
    type ty = Types.ty
    datatype enventry = VarEntry of {ty: ty}
                    |   FunEntry of {ty: ty}
    datatype tenventry = TyEntry of {ty: ty}
                    |  TyConEntry of {tycon: Types.tycon}
    
    val base_tenv = Symbol.empty
    val base_venv = Symbol.empty
end
