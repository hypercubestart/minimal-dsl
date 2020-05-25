use "semant.sml";

structure A = AbSyntax;
structure S = Symbol;
structure E = Env;
structure T = Types;

structure Evaluate =
struct
  datatype exp = IntExp of int 
                    | StringExp of string
                    | ArrayExp of exp list
                    | RecordExp of (S.symbol * exp) list
                    | FunctionExp of exp S.table option ref * S.symbol list * A.exp (*closure*)
                    | NilExp
end

structure Interpreter =
struct
  fun zip(l::lrest, r::rrest) = (l,r) :: zip(lrest, rrest)
  |   zip([], []) = []

(* TYPE CHECKING *)
  fun base_tenv() =
    let val base_tenv: Types.ty S.table = S.empty
        val base_tenv = S.enter(base_tenv, S.symbol "int", Types.INT)
        val base_tenv = S.enter(base_tenv, S.symbol "string", Types.STRING)
        val base_tenv = S.enter(base_tenv, S.symbol "nil", Types.NIL)
        val base_tenv = S.enter(base_tenv, S.symbol "unit", Types.UNIT)
      in base_tenv
    end

  fun type_check(exp) = 
    let val base_venv: E.enventry S.table = S.empty
        val base_tenv: Types.ty S.table = base_tenv()
    in 
      Semant.transExp(base_venv, base_tenv)(exp)
    end

(* EVALUATE/INTERPRET *)
  fun transExp(venv, A.VarExp(var)) = trvar(venv, var)
  |   transExp(venv, A.NilExp) = Evaluate.NilExp
  |   transExp(venv, A.IntExp(i)) = Evaluate.IntExp i
  |   transExp(venv, A.StringExp(s)) = Evaluate.StringExp s
  |   transExp(venv, A.CallExp{func, args}) = 
        let val Evaluate.FunctionExp(ref(SOME(fenv)), symbols, body) = transExp(venv, func)
            fun mapper(arg) = transExp(venv, arg)
            val args' = map mapper args
            val zip = zip(symbols, args')
            fun foldF((s, a), venv) = S.enter(venv, s, a)
            val venv' = foldr foldF fenv zip
        in transExp(venv', body)
        end
  |   transExp(venv, A.OpExp{left, oper, right}) = 
        let val Evaluate.IntExp(l) = transExp(venv, left)
            val Evaluate.IntExp(r) = transExp(venv, right)
        in  (
          case oper of A.PlusOp => Evaluate.IntExp(l + r)
          | A.MinusOp => Evaluate.IntExp(l - r)
          | A.LessOp => Evaluate.IntExp(if l < r then 1 else 0)
          | A.LessEqualOp => Evaluate.IntExp(if l <= r then 1 else 0)
        )
        end
  |   transExp(venv, A.RecordExp{fields, typ}) =
        let fun mapper(symbol, exp) = (symbol, transExp(venv, exp))
        in Evaluate.RecordExp(map mapper fields)
        end
  |   transExp(venv, A.SeqExp(exps)) = 
        let fun seqList(e::[]) = transExp(venv, e)
        |   seqList(e::elist) = (transExp(venv, e); seqList(elist))
        in seqList(exps)
        end
  |   transExp(venv, A.AssignExp{var, exp}) = Evaluate.NilExp (*NOT ALLOWING ASSIGN*)
  |   transExp(venv, A.LetExp{decs, body}) =
        let val venv' = transDecs(venv, decs)
        in  transExp(venv', body)
        end
  |   transExp(venv, A.ArrayExp{typ, size, init}) = 
        let val Evaluate.IntExp(arraysize) = transExp(venv, size)
            fun initer(i) = transExp(venv, init)
            val arr = List.tabulate(arraysize, initer)
        in  Evaluate.ArrayExp(arr)
        end
  |   transExp(venv, A.IfExp{cond, first, second}) = 
        let
          val Evaluate.IntExp(condVal) = transExp(venv, cond)
        in
          if condVal = 1 then transExp(venv, first) else transExp(venv, second)
        end
  and trvar(venv, A.SimpleVar(symbol)) = 
        let
          val SOME(var) = S.look(venv, symbol)
        in
          var
        end
  | trvar(venv, A.FieldVar(var, symbol)) = 
        let
          val Evaluate.RecordExp(record) = trvar(venv, var)
          fun filterEquals(s,  exp) = s = symbol
          val fields = List.filter filterEquals record
        in
          (
            case fields of x::[] => #2 x
          )
        end
  | trvar(venv, A.SubscriptVar(var, exp)) = 
        let
          val Evaluate.IntExp(index) = transExp(venv, exp)
          val Evaluate.ArrayExp(list) = trvar(venv, var)
        in 
          List.nth(list, index)
        end
  (* DECLARATIONS *)
  and transDecs(venv, []) = venv
  | transDecs(venv, x::xs) = 
      let val venv' = transDec(venv, x) 
      in transDecs(venv', xs)
      end 
  and transDec(venv, A.FunctionDec(fundecs)) = 
      let fun single(fundec: A.fundec, venv) = (
            let val formals = map #name (#params fundec)
            in S.enter(venv, #name fundec, Evaluate.FunctionExp(ref(NONE), formals, #body fundec))
            end
          )
          val venv' = foldr single venv fundecs
          (*iterate through each fundec again and update venv to enable RECURSIVE FUNCTION*)
          fun foldF(fundec: A.fundec, venv') = (
            let val SOME(Evaluate.FunctionExp(env_ref, formals, body)) = S.look(venv', #name fundec)
            in env_ref := SOME(venv'); venv'
            end
          )
      in foldr foldF venv' fundecs
      end
  | transDec(venv, A.VarDec{name, escape, typ, init}) = S.enter(venv, name, transExp(venv, init))
  | transDec(venv, A.TypeDec typedecs) = venv (*no op*)


  fun evaluate(exp) = 
    let val base_venv: Evaluate.exp S.table = S.empty
    in transExp(base_venv, exp)
    end

  (* we don't need to keep track venv/tenv because cannot be modified between statements *)
  fun interpret(exp) = (type_check(exp); evaluate(exp))
end