(* mmonomorphic DSL with first class functions *)
use "semant.sml";

structure A = AbSyntax;
structure S = Symbol;
structure E = Env;
structure T = Types;

fun base_tenv() =
  let val base_tenv: Types.ty S.table = S.empty
      val base_tenv = S.enter(base_tenv, S.symbol "int", Types.INT)
      val base_tenv = S.enter(base_tenv, S.symbol "string", Types.STRING)
      val base_tenv = S.enter(base_tenv, S.symbol "nil", Types.NIL)
      val base_tenv = S.enter(base_tenv, S.symbol "unit", Types.UNIT)
      in base_tenv
  end;

fun type_checker(exp) = 
  let val base_venv: E.enventry S.table = S.empty
      val base_tenv: Types.ty S.table = base_tenv()
    in 
      Semant.transExp(base_venv, base_tenv)(exp)
  end;

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
    val tc = type_checker(exp)
in 
  print "exp1 done----------------\n"; tc
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
    val tc = type_checker(exp)
in 
  print "exp2 done----------------\n"; tc
end;
