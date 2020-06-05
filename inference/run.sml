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