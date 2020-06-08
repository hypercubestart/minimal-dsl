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
  val listItems : 'a table -> 'a list
  val contains: 'a table * symbol -> bool
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
    fun listItems(t: 'a table) = IntBinaryMap.listItems t     
    fun contains(t: 'a table, s: symbol) = (
        case look(t, s) of
           SOME(_) => true
        |  NONE => false
    )          
end
(* --------------AST--------------- *)
structure AbSyntax =
struct
type symbol = Symbol.symbol

datatype var = SimpleVar of symbol
            |  SubscriptVar of var * exp

and exp = 
    VarExp of var
|   NilExp
|   IntExp of int
|   StringExp of string
|   CallExp of {func: exp, args: exp}
|   OpExp of {left: exp, oper: oper, right: exp}
|   ConstructorExp of {con: symbol, args: exp list}
|   SeqExp of exp list
|   LetExp of {decs: dec list, body: exp}
|   ArrayExp of {typ: ty, size: exp, init: exp}
|   IfExp of {cond: exp, first: exp, second: exp}
|   IsNilExp of exp

and dec = 
    FunctionDec of fundec list
|   VarDec of {name: symbol, init: exp, typ: ty option}
|   TypeDec of tydec list

and tydec =
    ParametricDec of symbol * tyvars * ty
|   ArrayDec of symbol * tyvars * ty
|   ADTDec of symbol * tyvars * (symbol * ty list) list

and ty = NameTy of symbol
    |    FuncTy of ty * ty
    |    TyCon of symbol * tyargs
    |    TupleTy of ty list

and oper = PlusOp | MinusOp | LessOp | LessEqualOp
withtype field = {name: symbol, typ: ty}
and fundec = {name: symbol, param: symbol, body: exp}
and tyvars = symbol list
and tyargs = ty list
end

(* Types *)
structure Types =
struct
  type unique = unit ref
  type symbol = Symbol.symbol

  datatype ty = Nil
            |   App of tycon * ty list
            |   Var of tyvar
            |   Meta of tymeta
            |   Poly of tyvar list * ty
            |   Constructor of ty * ty
            |   Tuple of ty list
  and tycon = Int 
            | String 
            | Unit 
            | Arrow
            | Array
            | TyFun of tyvar list * ty
            | Unique of tycon option ref * unique
            | ADT of symbol list
  withtype tyvar = int  
  and tymeta = int  
end

(* Environment *)
signature ENV =
sig
  (* type access *)
  (* type ty *)
  datatype enventry = VarEntry of {ty:Types.ty}
                    | FunEntry of {ty:Types.ty}
  datatype tenventry = TyEntry of {ty:Types.ty}
                    |  TyConEntry of {tycon: Types.tycon}
  val base_tenv : tenventry Symbol.table (*predefined types*)
  val base_venv : Types.ty Symbol.table (*predefined functions*)
end

structure Env :> ENV =
struct
    type ty = Types.ty
    datatype enventry = VarEntry of {ty: ty}
                    |   FunEntry of {ty: ty}
    datatype tenventry = TyEntry of {ty: ty}
                    |    TyConEntry of {tycon: Types.tycon}
    
    val base_tenv = Symbol.empty
    val base_venv = Symbol.empty
end
