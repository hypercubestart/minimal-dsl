(*  *)
use "semant.sml";

structure A = AbSyntax;
structure S = Symbol;
structure E = Env;
structure T = Types;

fun base_tenv() =
  let val base_tenv: E.tenventry S.table = S.empty
      val base_tenv' = S.enter(base_tenv, S.symbol "int", E.TyConEntry{tycon=T.Int})
      val base_tenv'' = S.enter(base_tenv', S.symbol "string", E.TyConEntry{tycon=T.String})
      in base_tenv''
  end;

fun type_checker(exp) = 
  let val base_venv: E.enventry S.table = S.empty
      val base_tenv: E.tenventry S.table = base_tenv()
    in 
      Semant.transExp(base_venv, base_tenv)(exp)
  end;

(* let type node<a> = {field: a}
in [node<int>{field: int}, 
    node<string>{field: "a"}]
end *)
let val exp = A.LetExp{
  decs=[
    A.TypeDec [
      A.RecordTyDec(S.symbol "node", [S.symbol "a"], [(S.symbol "field", A.NameTy (S.symbol "a"))])
    ]
  ],
  body=A.SeqExp[
    A.RecordExp{typ=S.symbol "node", tyargs=[A.NameTy(S.symbol "int")], fields=[(S.symbol "field", A.IntExp 1)]},
    A.RecordExp{typ=S.symbol "node", tyargs=[A.NameTy(S.symbol "string")], fields=[(S.symbol "field", A.StringExp "a")]}
  ]
}
    val tc = type_checker(exp)
in 
  print "exp1 done----------------\n"; tc
end;
