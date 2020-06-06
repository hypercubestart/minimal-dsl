use "interpreter.sml";

val run = Interpreter.interpret;

(* let
  fun id(x) = x
in
  id(5); id("hi")
end *)
let
  val exp = A.LetExp{
    decs=[
      A.FunctionDec([
        {
          name = S.symbol "id",
          param = S.symbol "x",
          body = A.VarExp(A.SimpleVar(S.symbol "x"))
        }: A.fundec
      ])
    ],
    body=A.SeqExp([
      A.CallExp{
        func=A.VarExp(A.SimpleVar(S.symbol "id")),
        args=A.IntExp(5)
      },
      A.CallExp{
        func=A.VarExp(A.SimpleVar(S.symbol "id")),
        args=A.StringExp("hii")
      }
    ])
  }
in
  run(exp)
end;

(* let fun rec(i) = if 0 < i then 1 + rec2(i - 1) else 0
       fun rec2(i) = if 0 < i then 1 + rec(i - 1) else 0
in rec(5)
end *)

let val exp = A.LetExp({decs= [
  A.FunctionDec([
    {
      name=S.symbol "rec", 
      param=S.symbol "i", 
      body=A.IfExp{
        cond=A.OpExp{left=A.IntExp(0), oper=A.LessOp, right=A.VarExp(A.SimpleVar (S.symbol "i"))},
        first=A.OpExp{
          left=A.IntExp(1), 
          oper=A.PlusOp, 
          right=A.CallExp{func=A.VarExp(A.SimpleVar (S.symbol "rec2")), args=
            A.OpExp{left=A.VarExp(A.SimpleVar(S.symbol "i")), oper=A.MinusOp, right = A.IntExp(1)}
          }
        },
        second = A.IntExp(0)
      }
    }: A.fundec,
    {
      name=S.symbol "rec2", 
      param=S.symbol "i", 
      body=A.IfExp{
        cond=A.OpExp{left=A.IntExp(0), oper=A.LessOp, right=A.VarExp(A.SimpleVar (S.symbol "i"))},
        first=A.OpExp{
          left=A.IntExp(1), 
          oper=A.PlusOp, 
          right=A.CallExp{func=A.VarExp(A.SimpleVar (S.symbol "rec")), args=
            A.OpExp{left=A.VarExp(A.SimpleVar(S.symbol "i")), oper=A.MinusOp, right = A.IntExp(1)}
          }
        },
        second = A.IntExp(0)
      }
    }: A.fundec
  ])
], 
body= A.CallExp{func=A.VarExp(A.SimpleVar(S.symbol "rec")), args=A.IntExp(5)}
})
in 
  run(exp)
end;

(* let
  type list<e> = {head: e, tail: list<e>}
in nil
end *)
let
  val list = A.RecordDec(
    S.symbol "list",
    [S.symbol "e"],
    [
      {name=S.symbol "head", typ=A.NameTy(S.symbol "e")}: A.field,
      {name=S.symbol "tail", typ=A.TyCon(S.symbol "list", [A.NameTy(S.symbol "e")])}: A.field
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

(* let
  type rec<e> = {head: e, tail: e}
  fun sum(a) = a.head + a.tail
in 
end *)

let
  val recordty = A.RecordDec(
    S.symbol "rec",
    [S.symbol "e"],
    [
      {name=S.symbol "head", typ=A.NameTy(S.symbol "e")}: A.field,
      {name=S.symbol "tail", typ=A.NameTy(S.symbol "e")}: A.field
    ]
  )

  val exp = A.LetExp{
    decs=[
      A.TypeDec([recordty]),
      A.FunctionDec[{
        name = S.symbol "sum",
        param = S.symbol "a",
        body=A.OpExp{
              left=A.VarExp(A.FieldVar(A.VarExp(A.SimpleVar(S.symbol "a")), S.symbol "head")),
              oper=A.PlusOp,
              right=A.VarExp(A.FieldVar(A.VarExp(A.SimpleVar(S.symbol "a")), S.symbol "tail"))
            }
      }: A.fundec]
    ],
    body=A.CallExp{
      func=A.VarExp(A.SimpleVar(S.symbol "sum")),
      args=A.RecordExp{fields=[
        (S.symbol "head", A.IntExp(3)), (S.symbol "tail", A.IntExp(1))
      ], typ=S.symbol "rec"}
    }
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
      {name=S.symbol "head", typ=A.NameTy(S.symbol "e")}: A.field,
      {name=S.symbol "tail", typ=A.TyCon(S.symbol "list", [A.NameTy(S.symbol "e")])}: A.field
    ]
  )

  fun toIntList([]) = A.VarExp(A.SimpleVar(S.symbol "nil"))
    | toIntList(i::ilist) = A.RecordExp{
    fields=[(S.symbol "head", A.IntExp i), (S.symbol "tail", toIntList(ilist))],
    typ=S.symbol "list"
  }

  val exp = A.LetExp{
    decs=[
      A.TypeDec([list]),
      A.VarDec{
        name=S.symbol "nil", 
        typ=SOME(A.TyCon(S.symbol "list", [A.NameTy(S.symbol "int")])), 
        init=A.NilExp
      },
      A.FunctionDec[{
        name = S.symbol "sum",
        param = S.symbol "a",
        body=A.IfExp{cond=A.IsNilExp(A.VarExp(A.SimpleVar(S.symbol "a"))), 
            first=A.IntExp(0),
            second=A.OpExp{
              left=A.VarExp(A.FieldVar(A.VarExp(A.SimpleVar(S.symbol "a")), S.symbol "head")),
              oper=A.PlusOp,
              right=A.CallExp{func=A.VarExp(A.SimpleVar(S.symbol "sum")), 
                args=A.VarExp(A.FieldVar(A.VarExp(A.SimpleVar(S.symbol "a")), S.symbol "tail"))
              }
            }
        }
      }: A.fundec]
    ],
    body=A.CallExp{
      func=A.VarExp(A.SimpleVar(S.symbol "sum")),
      args=toIntList([1,2,3])
    }
  }
in
  run(exp)
end;