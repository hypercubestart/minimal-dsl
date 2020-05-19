use "ast.sml";

(* Semantics/Type checking *)
structure Translate =
struct
  type exp = unit
end

structure Semant =
struct
  type ty = Types.ty
  type venv = Env.enventry Symbol.table
  type tenv = ty Symbol.table

  type expty = {exp: Translate.exp, ty: Types.ty}

  (* transVar: venv * tenv * AbSyntax.var -> expty
  transExp: venv * tenv * AbSyntax.exp -> expty
  transDec: venv * tenv * AbSyntax.dec -> {venv: venv, tenv: tenv}
  transTy:          tenv * AbSyntax.ty -> Types.ty *)
  structure A = AbSyntax
  structure S = Symbol
  structure E = Env

  fun checkInt({exp,ty}) = case ty of Types.INT => ()
                        |  _ => print "-----------------integer required\n";

  fun actual_ty(ty) = case ty of Types.NAME(symbol, ref(SOME(t))) => t (*might not be right*)
                                  |  _ => ty

  fun checkCallTypes(argTypes, formals) = (
    case argTypes of [] => (
      case formals of [] => ()
                    | f::fs => print "more parameters than arguments\n"
    )
    | x::xs => (
      case formals of [] => print "more arguments than parameters"
                    | f::fs => if x = f then checkCallTypes(xs,fs) else print "wrong argument type\n"
    )
  )

  fun printType(ty) =
    case ty of Types.INT => print "INT"
            |  Types.STRING => print "STRING"
            |  Types.RECORD(fields, _) => 
                  let fun mapper(symbol, ty) = printType(ty)
                    in print ("RECORD"); map mapper fields; ()
                  end
            |  Types.ARRAY(_, _) => print "ARRAY"
            |  Types.NIL => print "Types.NIL"
            |  Types.UNIT => print "TYPES.UNIT"
            |  Types.NAME(_, _) => print "TYPES.NAME"

  fun transExp(venv, tenv) = 
    let fun trexp(A.VarExp var) =
                  trvar(var)
          | trexp (A.NilExp) = (print("trexp(A.NilExp) reached?!!?"); {exp=(), ty=Types.NIL})
          | trexp(A.IntExp int) = 
                  {exp=(), ty=Types.INT}
          | trexp(A.StringExp string) = 
                  {exp=(), ty=Types.STRING}
          | trexp(A.CallExp{func, args}) =
              let val SOME(enventry) = S.look(venv, func)
                in (
                  case enventry of E.VarEntry{ty} => (print "not a func!!\n"; {exp=(), ty=Types.NIL})
                                |  E.FunEntry{formals, result} =>
                    let val argExps = map trexp args
                        val argTypes = map #ty argExps
                    in (checkCallTypes(argTypes, formals); {exp=(), ty=Types.INT})
                    end
                ) 
              end
          | trexp(A.OpExp{left, oper, right}) =
                  (checkInt(trexp left);
                  checkInt(trexp right);
                  {exp=(), ty=Types.INT})
          | trexp(A.RecordExp{fields, typ}) = (* FIX THIS! only checks exp fields in record type *)
              let val SOME(Types.RECORD(record_field, unique)) = S.look(tenv, typ)
                  fun checkField(symbol, exp) = 
                    let fun filterEqual(field_name: S.symbol, ty: ty) = symbol = field_name
                        val record_type: (Symbol.symbol * ty) list = List.filter filterEqual record_field
                      in case record_type of
                        [] => print "field name not found"
                      | x::[] => 
                          let val trexp = trexp(exp)
                            in if #ty trexp = actual_ty(#2 x) then () else (print "field type incorrect"; printType(#2 x); printType(#ty trexp))
                          end
                    end
                in map checkField fields; {exp=(), ty = Types.RECORD(record_field, unique)}
              end
          | trexp(A.SeqExp exp_list) =
              let fun trSeqExp(exp_list) = 
                  (case exp_list of [] => (print "SeqExp empty"; {exp=(), ty=Types.NIL})
                                 |  x::[] => trexp(x)
                                 |  x::xs => (trexp(x); trSeqExp(xs)))
                in trSeqExp(exp_list)
              end
          | trexp(A.AssignExp{var, exp}) =
                  trexp(exp)
          | trexp(A.LetExp{decs, body}) = 
              let val {venv=venv', tenv=tenv'} = transDecs(venv,tenv,decs)
                in transExp(venv',tenv') body
              end
          | trexp(A.ArrayExp{typ, size, init}) = (* FIX THIS *)
              let val {exp, ty} = trexp(init)
                  val SOME(array_ty) = S.look(tenv, typ)
                in if ty = array_ty then {exp=(), ty=Types.ARRAY(ty, ref(()))} else (print "ArrayExp init type fail"; {exp=(), ty=Types.NIL})
              end

          (* trvar *)
        and trvar(A.SimpleVar id) = 
            (case S.look(venv, id) of
              SOME(E.VarEntry{ty}) => {exp=(), ty=ty}
            | NONE => (print ("-------------undefined variable" ^ S.name id);
                      {exp=(), ty=Types.NIL}))
          | trvar(A.FieldVar(var, symbol)) =
            let val {exp, ty} = trvar(var)
              in case ty of Types.RECORD(fieldlist, unique) => 
                let fun filterEqual(field_name: S.symbol, ty: ty) = symbol = field_name
                    val filtered = List.filter filterEqual fieldlist
                  in case filtered of [] => (print ("-------------undefined record field name");
                                        {exp=(), ty=Types.NIL})
                                |  x::[] => {exp=(), ty= #2 x}
                end
                | _ => (print("record type required"); {exp=(), ty=Types.NIL})
            end 
          | trvar(A.SubscriptVar(var, exp)) =
              let val arr = trvar(var)
                  val subscript = trexp(exp)
                in checkInt(subscript); 
                   case #ty arr of Types.ARRAY(ty, unique)=> {exp=(), ty= #ty arr}
                        |  _ => (print "-----------------array required\n"; {exp=(), ty=Types.NIL})
              end
    in trexp
    end
  (*transform declarations*)
  and transDecs(venv, tenv, []) = {venv=venv, tenv=tenv}
    | transDecs(venv, tenv, x::xs) = 
        let val {venv=venv', tenv=tenv'} = transDec(venv, tenv, x) 
          in transDecs(venv', tenv', xs)
        end 
  and transDec(venv, tenv, A.VarDec{name, typ, init=AbSyntax.NilExp, escape}) =
      (case typ of SOME(symbol) => 
        let val SOME(ty) = S.look(tenv, symbol)
          in    {tenv=tenv,
              venv=S.enter(venv, name, E.VarEntry{ty=ty})}
        end
      | NONE => (print("NIL needs record type"); {tenv=tenv,venv=venv}))
    | transDec(venv, tenv, A.VarDec{name, typ, init, escape}) = 
      let val {exp,ty} = transExp(venv, tenv)(init)
        in {tenv=tenv,
            venv=S.enter(venv, name, E.VarEntry{ty=ty})}
      end
    | transDec(venv, tenv, A.TypeDec[{name, ty}]) = (* ONLY HANDES SINGLE TYPE DECLARATION *)
    (* first enter type into tenv to handle recursive types *)
      let val tenv' = S.enter(tenv, name, Types.NAME(name, ref NONE))
          val ty = transTy(tenv', ty)
          fun subst(tenv, Types.RECORD(recordList, unique)) = 
            let fun mapper(symbol, ty) = subst(tenv, ty);
              in map mapper recordList; ()
            end
            | subst(tenv, Types.NAME(symbol, ty_ref)) =
              (case ty_ref of ref(NONE) =>
                let val SOME(ty) = S.look(tenv, symbol)
                  in ty_ref := SOME(ty); ()
                end
                              |  _ => ())
            | subst(tenv, ty) = ()
          val tenv'' = S.enter(tenv, name, ty)
        in subst(tenv'', ty); {venv = venv, tenv = tenv''}
      end
    | transDec(venv, tenv, A.FunctionDec(fundecs)) =
    (* first process function header to handle recursive functions *)
      let
        
        fun processFunctionHeader({name, params, result=SOME(rt), ...}: A.fundec, venv) = 
          let val SOME(result_ty) = S.look(tenv, rt)
              fun transparam{name, typ, escape} = case S.look(tenv, typ)
                                      of SOME t => {name=name, ty=t}
              val params' = map transparam params
            in S.enter(venv, name, E.FunEntry({formals=map #ty params', result=result_ty})) 
          end
        val venv' = foldr processFunctionHeader venv fundecs

        fun checkFunction({params, result=SOME(rt), body, ...}: A.fundec, venv) = 
          let 
            val SOME(result_ty) = S.look(tenv, rt)
            fun transparam{name, typ, escape} = case S.look(tenv, typ)
                                      of SOME t => {name=name, ty=t}
            val params' = map transparam params
            fun enterparam({name, ty}, venv) = S.enter(venv, name, E.VarEntry{ty=ty})
            val venv'' = foldr enterparam venv' params'

            in transExp(venv'', tenv) body;
            venv
          end
      in foldr checkFunction venv' fundecs;
        {venv=venv', tenv=tenv}
      end
  and transTy(tenv, AbSyntax.NameTy(symbol)) = 
        let val SOME(ty) = S.look(tenv, symbol)
          in ty
        end
    | transTy(tenv, AbSyntax.ArrayTy(symbol)) =
        let val SOME(ty) = S.look(tenv, symbol)
          in ty
        end
    | transTy(tenv, AbSyntax.RecordTy(fields)) = 
        let val unique = ref(())
            fun mapper(field: AbSyntax.field) = 
              let val SOME(ty) = S.look(tenv, #typ field)
                in (#name field, ty)
              end
          in Types.RECORD(map mapper fields, unique)
        end
end