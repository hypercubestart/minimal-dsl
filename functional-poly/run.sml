use "interpreter.sml";

val run = Interpreter.interpret;

(* let
  fun<a> id(x) = x
in
  id(5); id("hi")
end *)
let
  val exp = A.LetExp{
    decs=[
      A.FunctionDec([
        {
          name = S.symbol "id",
          param = {name=S.symbol "x", escape=ref(true), typ=A.NameTy(S.symbol "a")}: A.field,
          tyvars = [S.symbol "a"],
          result = A.NameTy(S.symbol "a"),
          body = A.VarExp(A.SimpleVar(S.symbol "x"))
        }: A.fundec
      ])
    ],
    body=A.SeqExp([
      A.CallExp{
        func=A.VarExp(A.SimpleVar(S.symbol "id")),
        tyargs=[A.NameTy(S.symbol "int")],
        args=A.IntExp(5)
      },
      A.CallExp{
        func=A.VarExp(A.SimpleVar(S.symbol "id")),
        tyargs=[A.NameTy(S.symbol "string")],
        args=A.StringExp("hii")
      }
    ])
  }
in
  run(exp)
end;

(* let
  type list<e> = {head: e, tail: list<e>}
  var nil: list<int> = nil
in nil
end *)
let
  val list = A.RecordDec(
    S.symbol "list",
    [S.symbol "e"],
    [
      {name=S.symbol "head", escape=ref(true), typ=A.NameTy(S.symbol "e")}: A.field,
      {name=S.symbol "tail", escape=ref(true), typ=A.TyCon(S.symbol "list", [A.NameTy(S.symbol "e")])}: A.field
    ]
  )
  val exp = A.LetExp{
    decs=[
      A.TypeDec([list]),
      A.VarDec{
        name=S.symbol "nil", 
        escape=ref(true), 
        typ=A.TyCon(S.symbol "list", 
        [A.NameTy(S.symbol "int")]), init=A.NilExp
      }
    ],
    body=A.VarExp(A.SimpleVar(S.symbol "nil"))
  }
in
  run(exp)
end;


(* let
  type list<e> = {head: e, tail: list<e>}
  fun sum(a) = if a=nil then 0 else a.head + sum(a.tail)
in 
end *)

let
  val list = A.RecordDec(
    S.symbol "list",
    [S.symbol "e"],
    [
      {name=S.symbol "head", escape=ref(true), typ=A.NameTy(S.symbol "e")}: A.field,
      {name=S.symbol "tail", escape=ref(true), typ=A.TyCon(S.symbol "list", [A.NameTy(S.symbol "e")])}: A.field
    ]
  )
  fun toIntList([]) = A.VarExp(A.SimpleVar(S.symbol "nil"))
    | toIntList(i::ilist) = A.RecordExp{
    fields=[(S.symbol "head", A.IntExp i), (S.symbol "tail", toIntList(ilist))],
    tyargs=[A.NameTy(S.symbol "int")],
    typ=S.symbol "list"
  }

  val exp = A.LetExp{
    decs=[
      A.TypeDec([list]),
      A.VarDec{
        name=S.symbol "nil", 
        escape=ref(true), 
        typ=A.TyCon(S.symbol "list", 
        [A.NameTy(S.symbol "int")]), init=A.NilExp
      },
      A.FunctionDec[{
        name = S.symbol "sum",
        param = {name=S.symbol "a", escape=ref(true), typ=A.TyCon(S.symbol "list", [A.NameTy(S.symbol "int")])},
        tyvars=[],
        result=A.NameTy(S.symbol "int"),
        body=A.IfExp{cond=A.IsNilExp(A.VarExp(A.SimpleVar(S.symbol "a"))), 
            first=A.IntExp(0),
            second=A.OpExp{
              left=A.VarExp(A.FieldVar(A.SimpleVar(S.symbol "a"), S.symbol "head")),
              oper=A.PlusOp,
              right=A.CallExp{func=A.VarExp(A.SimpleVar(S.symbol "sum")), 
                tyargs=[], 
                args=A.VarExp(A.FieldVar(A.SimpleVar(S.symbol "a"), S.symbol "tail"))
              }
            }
        }
      }: A.fundec]
    ],
    body=A.CallExp{func=A.VarExp(A.SimpleVar(S.symbol "sum")), tyargs=[], args=toIntList([1,2,3,4])}
  }
in
  run(exp)
end;