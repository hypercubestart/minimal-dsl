(*execute using interpreter*)
use "interpreter.sml";

val run = Interpreter.interpret;

(* let fun inc(x) = x + 1
in inc
end *)
let val exp = A.LetExp({decs= [
  A.FunctionDec([
    {name=S.symbol "inc", params=[{name=S.symbol "i", escape=ref true, typ=A.NameTy(S.symbol "int")}: A.field], result=SOME(A.NameTy(S.symbol "int")),
    body=A.OpExp({left=A.VarExp(A.SimpleVar(S.symbol "i")), oper=A.PlusOp, right=A.IntExp(1)})}: A.fundec
  ])
], 
body= A.VarExp(A.SimpleVar(S.symbol "inc"))
})
in 
  run(exp)
end;

(*
let fun add(x) = 
        let fun inc(y) = y + x
        in inc
        end
in add(5)(2)
end
*)
let val exp = A.LetExp({decs= [
  A.FunctionDec([
    {
        name=S.symbol "add", 
        params=[{name=S.symbol "x", escape=ref true, typ=A.NameTy(S.symbol "int")}: A.field], 
        result=SOME(A.FuncTy([A.NameTy(S.symbol "int")], A.NameTy(S.symbol "int"))),
        body= A.LetExp{
            decs= [
                A.FunctionDec[{
                    name=S.symbol "inc", 
                    params=[{name=S.symbol "y", escape=ref true, typ=A.NameTy(S.symbol "int")}: A.field], 
                    result=SOME(A.NameTy(S.symbol "int")),
                    body=A.OpExp{left=A.VarExp(A.SimpleVar(S.symbol "y")), oper=A.PlusOp, right=A.VarExp(A.SimpleVar(S.symbol "x"))}
                }: A.fundec]
            ], 
            body= A.VarExp(A.SimpleVar(S.symbol "inc"))
        }
    }: A.fundec
  ])
], 
body=A.CallExp{func=A.CallExp{func=A.VarExp(A.SimpleVar(S.symbol "add")), args=[A.IntExp 5]}, args=[A.IntExp 2]}
})
in run(exp)
end;

(* let fun rec(i) = if 0 < i then 1 + rec(i - 1) else 0
in rec(5)
end *)
let val exp = A.LetExp({decs= [
  A.FunctionDec([
    {
      name=S.symbol "rec", 
      params=[{name=S.symbol "i", escape=ref true, typ=A.NameTy(S.symbol "int")}: A.field], 
      result=SOME(A.NameTy(S.symbol "int")),
      body=A.IfExp{
        cond=A.OpExp{left=A.IntExp(0), oper=A.LessOp, right=A.VarExp(A.SimpleVar (S.symbol "i"))},
        first=A.OpExp{
          left=A.IntExp(1), 
          oper=A.PlusOp, 
          right=A.CallExp{func=A.VarExp(A.SimpleVar (S.symbol "rec")), args=[
            A.OpExp{left=A.VarExp(A.SimpleVar(S.symbol "i")), oper=A.MinusOp, right = A.IntExp(1)}
          ]}
        },
        second = A.IntExp(0)
      }
    }: A.fundec
  ])
], 
body= A.CallExp{func=A.VarExp(A.SimpleVar(S.symbol "rec")), args=[A.IntExp(5)]}
})
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
      params=[{name=S.symbol "i", escape=ref true, typ=A.NameTy(S.symbol "int")}: A.field], 
      result=SOME(A.NameTy(S.symbol "int")),
      body=A.IfExp{
        cond=A.OpExp{left=A.IntExp(0), oper=A.LessOp, right=A.VarExp(A.SimpleVar (S.symbol "i"))},
        first=A.OpExp{
          left=A.IntExp(1), 
          oper=A.PlusOp, 
          right=A.CallExp{func=A.VarExp(A.SimpleVar (S.symbol "rec2")), args=[
            A.OpExp{left=A.VarExp(A.SimpleVar(S.symbol "i")), oper=A.MinusOp, right = A.IntExp(1)}
          ]}
        },
        second = A.IntExp(0)
      }
    }: A.fundec,
    {
      name=S.symbol "rec2", 
      params=[{name=S.symbol "i", escape=ref true, typ=A.NameTy(S.symbol "int")}: A.field], 
      result=SOME(A.NameTy(S.symbol "int")),
      body=A.IfExp{
        cond=A.OpExp{left=A.IntExp(0), oper=A.LessOp, right=A.VarExp(A.SimpleVar (S.symbol "i"))},
        first=A.OpExp{
          left=A.IntExp(1), 
          oper=A.PlusOp, 
          right=A.CallExp{func=A.VarExp(A.SimpleVar (S.symbol "rec")), args=[
            A.OpExp{left=A.VarExp(A.SimpleVar(S.symbol "i")), oper=A.MinusOp, right = A.IntExp(1)}
          ]}
        },
        second = A.IntExp(0)
      }
    }: A.fundec
  ])
], 
body= A.CallExp{func=A.VarExp(A.SimpleVar(S.symbol "rec")), args=[A.IntExp(5)]}
})
in 
  run(exp)
end;