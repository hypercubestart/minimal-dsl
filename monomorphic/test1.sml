(* testing version 1, ONLY TYPE CHECKING, NO ARRAYS/RECORDS *)
use "semant.sml";

structure A = AbSyntax;
structure S = Symbol;
structure E = Env;
structure T = Types;

fun base_tenv() =
  let val base_tenv: Types.ty S.table = S.empty
      val base_tenv' = S.enter(base_tenv, S.symbol "int", Types.INT)
      in base_tenv'
  end;

fun type_checker(exp) = 
  let val base_venv: E.enventry S.table = S.empty
      val base_tenv: Types.ty S.table = base_tenv()
    in 
      Semant.transExp(base_venv, base_tenv)(exp)
  end;

(* x = 1 + 1
2 + 2 *)
let val exp = A.SeqExp([
                A.AssignExp({var=A.SimpleVar(S.symbol "x"),
                  exp=A.OpExp({left=A.IntExp(1), oper=A.PlusOp, right=A.IntExp(1)})
                }),
                A.OpExp({left=A.IntExp(2), oper=A.MinusOp, right=A.IntExp(2)})
              ])
    val tc = type_checker(exp)
in 
  print "exp1 done----------------\n"; tc
end;

(* 1 + "hi" *)
let val exp = A.OpExp({left=A.IntExp(1), oper=A.PlusOp, right=A.StringExp("hi")})
    val tc = type_checker(exp)
in 
  print "exp2 done----------------\n"; tc
end;

(* let x = "hi" in x end *)
let val exp = A.LetExp({decs= [
  A.VarDec{name= S.symbol "x", escape= ref true, typ=NONE, init=A.StringExp("hi")}
], 
body= A.VarExp(A.SimpleVar(S.symbol "x"))
})
    val tc = type_checker(exp)
in 
  print "exp3 done----------------\n"; tc
end;

(* let fun inc(i) = i + 1, x = 1 in inc(x) end*)
let val exp = A.LetExp({decs= [
  A.VarDec({name= S.symbol "x", escape= ref true, typ=NONE, init=A.IntExp(1)}),
  A.FunctionDec([
    {name=S.symbol "inc", params=[{name=S.symbol "i", escape=ref true, typ=S.symbol "int"}: A.field], result=SOME(S.symbol "int"),
    body=A.OpExp({left=A.VarExp(A.SimpleVar(S.symbol "i")), oper=A.PlusOp, right=A.IntExp(1)})}: A.fundec
  ])
], 
body= A.CallExp({func=S.symbol "inc", args=[A.VarExp(A.SimpleVar(S.symbol "x"))]})
})
    val tc = type_checker(exp)
in 
  print "exp4 done----------------\n"; tc
end;

(* let fun inc(i) = i + 1, x = "hi" in inc(x) end*)
(* wrong argument type *)
let val exp = A.LetExp({decs= [
  A.VarDec({name= S.symbol "x", escape= ref true, typ=NONE, init=A.StringExp("hi")}),
  A.FunctionDec([
    {name=S.symbol "inc", params=[{name=S.symbol "i", escape=ref true, typ=S.symbol "int"}: A.field], result=SOME(S.symbol "int"),
    body=A.OpExp({left=A.VarExp(A.SimpleVar(S.symbol "i")), oper=A.PlusOp, right=A.IntExp(1)})}: A.fundec
  ])
], 
body= A.CallExp({func=S.symbol "inc", args=[A.VarExp(A.SimpleVar(S.symbol "x"))]})
})
    val tc = type_checker(exp)
in 
  print "exp5 done----------------\n"; tc
end;

(* mutually recursive functions *)
(* let fun a(b) = c(b) + 1 
       fun c(d) = a(d) - 1
   in a(b)
   end
*)
let val exp = A.LetExp({decs= [
  A.FunctionDec([
    {name=S.symbol "a", params=[{name=S.symbol "b", escape=ref true, typ=S.symbol "int"}: A.field], result=SOME(S.symbol "int"),
    body=A.OpExp({left=A.VarExp(A.SimpleVar(S.symbol "b")), oper=A.PlusOp, right=A.IntExp(1)})}: A.fundec,
    {name=S.symbol "c", params=[{name=S.symbol "d", escape=ref true, typ=S.symbol "int"}: A.field], result=SOME(S.symbol "int"),
    body=A.OpExp({left=A.VarExp(A.SimpleVar(S.symbol "d")), oper=A.PlusOp, right=A.IntExp(1)})}: A.fundec
  ])
], 
body= A.CallExp({func=S.symbol "a", args=[A.IntExp(1)]})
})
    val tc = type_checker(exp)
in 
  print "exp6 done----------------\n"; tc
end;

(* y = 1 + "hi" *)
(* let val exp = A.SeqExp([
                A.AssignExp({var=A.SimpleVar(S.symbol "y"),
                  exp=A.OpExp({left=A.IntExp(1), oper=A.PlusOp, right=A.StringExp("hi")})
                })
              ])
    val tc = type_checker(exp)
in 
  print "exp3 done----------------\n"; tc
end; *)
