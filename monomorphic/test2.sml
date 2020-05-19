(* testing version 2, ONLY TYPE CHECKING, WITH ARRAYS/RECORDS *)
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

(* let type coordinate = {x: int, y: int}
    fun add(c: coordinate) = c.x + c.y
    val coord: coordinate = {x: 1, y: 2}
    in add(coord)
end *)
let val exp = A.LetExp{decs=[
  A.TypeDec[
    {name=S.symbol "coordinate",
    ty=A.RecordTy
      [
        {name= S.symbol "x", escape= ref(true), typ= S.symbol "int"}: A.field,
        {name= S.symbol "y", escape= ref(true), typ= S.symbol "int"}: A.field
      ]
    }
  ],
  A.FunctionDec[
    {
      name = S.symbol "add",
      params=[{name=S.symbol "c", escape=ref(true), typ=S.symbol "coordinate"}: A.field],
      result=SOME(S.symbol "int"),
      body=A.OpExp{left=A.VarExp(A.FieldVar(A.SimpleVar(S.symbol "c"), S.symbol "x")), 
                  oper=A.PlusOp,
                  right=A.VarExp(A.FieldVar(A.SimpleVar(S.symbol "c"), S.symbol "y"))}
    }: A.fundec
  ],
  A.VarDec{name = S.symbol "coord", 
          escape=ref(true), 
          typ=NONE, 
          init=A.RecordExp{fields=[
            (S.symbol "x", A.IntExp(1)),
            (S.symbol "y", A.IntExp(2))
          ],typ=S.symbol "coordinate"}
  }
], 
body= A.IntExp(1)
}
    val tc = type_checker(exp)
in 
  print "ex1 done----------------\n"; tc
end;

(* let type list = {first: int, rest: list}
  in 1
end *)
let val exp = A.LetExp{decs=[
  A.TypeDec[
    {name=S.symbol "list",
    ty=A.RecordTy
      [
        {name= S.symbol "first", escape= ref(true), typ= S.symbol "int"}: A.field,
        {name= S.symbol "rest", escape= ref(true), typ= S.symbol "list"}: A.field
      ]
    }
  ],
  A.VarDec{name = S.symbol "nil", escape=ref(true), typ=SOME(S.symbol "list"), init=A.NilExp},
  A.VarDec{name = S.symbol "l", 
          escape=ref(true), 
          typ=NONE, 
          init=A.RecordExp{fields=[
            (S.symbol "first", A.IntExp(2)),
            (S.symbol "rest", A.VarExp(A.SimpleVar(S.symbol "nil")))
          ],typ=S.symbol "list"}
  }
], 
body= A.VarExp(A.SimpleVar(S.symbol "nil"))
}
    val tc = type_checker(exp)
in 
  print "ex2 done----------------\n"; tc
end;