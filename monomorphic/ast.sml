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
            |  SubscriptVar of var * exp

and exp = 
    VarExp of var
|   NilExp
|   IntExp of int
|   StringExp of string
|   CallExp of {func: symbol, args: exp list}
|   OpExp of {left: exp, oper: oper, right: exp}
|   RecordExp of {fields: (symbol * exp) list, typ: symbol}
|   SeqExp of exp list
|   AssignExp of {var: var, exp: exp}
|   LetExp of {decs: dec list, body: exp}
|   ArrayExp of {typ: symbol, size: exp, init: exp}

and dec = 
    FunctionDec of fundec list
|   VarDec of {name: symbol, escape: bool ref, typ: symbol option, init: exp}
|   TypeDec of {name: symbol, ty: ty} list

and ty = NameTy of symbol
    |    RecordTy of field list
    |    ArrayTy of symbol

and oper = PlusOp | MinusOp
withtype field = {name: symbol, escape: bool ref, typ: symbol}
and fundec = {name: symbol, params: field list, result: symbol option, body: exp}
end

(* Types *)
structure Types =
struct
  type unique = unit ref

  datatype ty = INT
            |   STRING
            |   RECORD of (Symbol.symbol * ty) list * unique
            |   ARRAY of ty * unique
            |   NIL
            |   UNIT
            |   NAME of Symbol.symbol * ty option ref
end

(* Environment *)
signature ENV =
sig
  (* type access *)
  (* type ty *)
  datatype enventry = VarEntry of {ty:Types.ty}
                    | FunEntry of {formals: Types.ty list, result: Types.ty}
  val base_tenv : Types.ty Symbol.table (*predefined types*)
  val base_venv : enventry Symbol.table (*predefined functions*)
end

structure Env :> ENV =
struct
    type ty = Types.ty
    datatype enventry = VarEntry of {ty: ty}
                    |   FunEntry of {formals: ty list, result: ty}
    
    val base_tenv = Symbol.empty
    val base_venv = Symbol.empty
end
