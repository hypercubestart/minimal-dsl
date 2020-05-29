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
  fun append(a,b) = if a=nil then b else {head=a.head, tail=append(a.tail, b)}
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
      A.TypeDec([list])
    ],
    body=A.NilExp
  }
in
  run(exp)
end;