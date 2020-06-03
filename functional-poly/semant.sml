use "ast.sml";

(* Semantics/Type checking *)
structure Translate =
struct
  type exp = unit
end

structure Semant =
struct
  type ty = Types.ty
  type venv = ty Symbol.table
  type tenv = Env.tenventry Symbol.table

  type expty = {exp: Translate.exp, ty: Types.ty}
  
  val nexttyvar = ref 0

  (* transVar: venv * tenv * AbSyntax.var -> expty
  transExp: venv * tenv * AbSyntax.exp -> expty
  transDec: venv * tenv * AbSyntax.dec -> {venv: venv, tenv: tenv}
  transTy:          tenv * AbSyntax.ty -> Types.ty *)
  structure A = AbSyntax
  structure S = Symbol
  structure E = Env
  structure T = Types

  exception TypeCheck

  fun checkInt(ty) = case ty of T.App(T.Int, []) => ()
                        |  _ => print "-----------------integer required\n";


  fun zip(a::al, b::bl) = (a,b)::zip(al, bl)
  |   zip([], []) = []

  fun printType(T.Nil) = print "Nil"
    | printType(T.App(tycon, tys)) = (print "App"; printTyCon(tycon))
    | printType(T.Var(tyvar)) = print "Var"
    | printType(T.Poly(tyvars, ty)) = print "Poly"
  and printTyCon(T.Int) = print "Int"
    | printTyCon(T.String) = print "String"
    | printTyCon(T.Unit) = print "Unit"
    | printTyCon(T.Arrow) = print "Arrow"
    | printTyCon(T.Array) = print "Array"
    | printTyCon(T.Record(fields)) = print "Record"
    | printTyCon(T.TyFun(tyvs, ty)) = print "TyFun"
    | printTyCon(T.Unique(ref(SOME(tycon)), unique)) = (print "Unique"; printTyCon(tycon))

  fun newtypevar() = 
    let val i = !nexttyvar
    in nexttyvar := i + 1; i
    end

  fun newtyvarlist(n) =
    if n > 0 then newtypevar()::newtyvarlist(n - 1) else []

  (*for unify, generate tyvar->ty mapping*)
  fun base_subst_tenv(v::vars, a::args) =
        let
          val tenv = base_subst_tenv(vars, args)
        in
          IntBinaryMap.insert(tenv, v, a)
        end
  |   base_subst_tenv([], []) = IntBinaryMap.empty

  (*enter symbol -> E.tenventry into tenv*)
  fun subst_tenv(tenv, v::vars, a::args) =
        let
          val tenv' = subst_tenv(tenv, vars, args)
        in
          S.enter(tenv', v, a)
        end
  |   subst_tenv(tenv, [], []) = tenv
  
  fun subst(T.Var(tyvar), tenv) = 
    (case IntBinaryMap.find(tenv, tyvar) of SOME(ty) => ty
    | NONE => T.Var(tyvar))
  |   subst(T.Nil, tenv) = T.Nil
  |   subst(T.App(T.TyFun(tyvars, t), tyargs), tenv) =
        subst(subst(t, base_subst_tenv(tyvars, tyargs)), tenv)
  |   subst(T.App(tycon, tyargs), tenv) = 
        let
          val tyargs' = map (fn x => subst(x, tenv)) tyargs
        in
          T.App(tycon, tyargs')
        end
  |   subst(T.Poly(tyvars, t), tenv) = 
        let
          val alphavars = newtyvarlist(length(tyvars))
          val alphavars' = map (fn x => T.Var(x)) alphavars
          val t' = subst(t, base_subst_tenv(tyvars, alphavars'))
        in
          T.Poly(alphavars, subst(t', tenv))
        end

  fun unify(T.App(T.Int, tyvars1), T.App(T.Int, tyvars2)) = unifylist(tyvars1, tyvars2)
  |   unify(T.App(T.String, tyvars1), T.App(T.String, tyvars2)) = unifylist(tyvars1, tyvars2)
  |   unify(T.App(T.Unit, tyvars1), T.App(T.Unit, tyvars2)) = unifylist(tyvars1, tyvars2)
  |   unify(T.App(T.Arrow, tyvars1), T.App(T.Arrow, tyvars2)) = unifylist(tyvars1, tyvars2)
  |   unify(T.App(T.Array, tyvars1), T.App(T.Array, tyvars2)) = unifylist(tyvars1, tyvars2)
  |   unify(T.App(T.Record(f1), tyvars1), T.App(T.Record(f2), tyvars2)) = 
        if f1 <> f2 then print("record fields cannot unify") else unifylist(tyvars1, tyvars2)
  |   unify(T.App(T.TyFun(tyvars, ty), tyargs), t) =
        unify(subst(ty, base_subst_tenv(tyvars, tyargs)), t)
  |   unify(t, T.App(T.TyFun(tyvars, ty), tyargs)) = 
        unify(subst(ty, base_subst_tenv(tyvars, tyargs)), t)
  |   unify(T.App(T.Unique(tycon1, u1), tyargs1), T.App(T.Unique(tycon2, u2), tyargs2)) =
        if u1 <> u2 then print("occurrence equivalence record failed") else unifylist(tyargs1, tyargs2)
  |   unify(T.Poly(tyvars1, t1), T.Poly(tyvars2, t2)) = 
        let
          val tyvar = map (fn x => T.Var(x)) tyvars1
        in
          unify(t1, subst(t2, base_subst_tenv(tyvars2, tyvar)))
        end
  |   unify(T.Var(a), T.Var(b)) = 
        if a <> b then print("diff tyvar") else ()
  |   unify(T.Nil, T.App(T.Record(_), _)) = ()
  |   unify(T.App(T.Record(_), _), T.Nil) = ()
  |   unify(a, b) = (printType(a); printType(b); print("unify failed"); raise TypeCheck)
  and unifylist(t1::t1list, t2::t2list) = (unify(t1, t2); unifylist(t1list, t2list))
  |   unifylist([], []) = ()

  fun expand(T.App(T.TyFun(tyvars, ty), tyargs)) = expand(subst(ty, base_subst_tenv(tyvars, tyargs)))
  |   expand(T.App(T.Unique(tycon, unique), tyargs)) = 
        let
          val SOME(tycon) = !tycon
        in
          expand(T.App(tycon, tyargs))
        end
  |   expand(u) = u

  fun transExp(venv, tenv) = 
    let fun trexp(A.VarExp var) =
                  trvar(var)
          | trexp(A.NilExp) = T.Nil
          | trexp(A.IntExp int) = T.App(T.Int, [])
          | trexp(A.StringExp str) = T.App(T.String, [])
          | trexp(A.CallExp{func, tyargs, args}) =
            let
              val tyargs' = map (fn x => transty(tenv, x)) tyargs
              val tf = trexp(func)
              val args' = trexp(args)
              val T.Poly(vars, T.App(T.Arrow, [t1, t2])) = expand(tf)
            in
              (unify(args', subst(t1, base_subst_tenv(vars, tyargs'))); subst(t2, base_subst_tenv(vars, tyargs')))
            end
          | trexp(A.OpExp{left, oper, right}) =
              (checkInt(trexp left);
              checkInt(trexp right);
              T.App(T.Int, []))
          | trexp(A.RecordExp{fields, tyargs, typ}) =
              let
                val SOME(E.TyConEntry{tycon}) = S.look(tenv, typ)
                val tyargs' = map (fn x => transty(tenv, x)) tyargs
                val t = T.App(tycon, tyargs')
                val T.App(T.Record(fieldnames), tys) = expand(t)
              in
                (List.tabulate(length(fields), (fn(i) => unify(List.nth(tys, i), trexp(#2(List.nth(fields, i))))));
                t)
              end
          | trexp(A.SeqExp exp_list) =
              let 
                fun trSeqExp(exp_list) = 
                  (case exp_list of [] => (print "SeqExp empty"; T.Nil)
                                 |  x::[] => trexp(x)
                                 |  x::xs => (trexp(x); trSeqExp(xs)))
              in trSeqExp(exp_list)
              end
          | trexp(A.AssignExp{var, exp}) =
              trexp(exp)
          | trexp(A.LetExp{decs, body}) = 
              let 
                fun transDec(dec, {venv,tenv}) = transdec(venv, tenv, dec)
                val {venv=venv', tenv=tenv'} = foldl transDec {venv=venv, tenv=tenv} decs
              in transExp(venv',tenv') body
              end
          | trexp(A.ArrayExp{typ, size, init}) = (print "ArrayExp reached??"; T.Nil) (*FIX THIS!*)
          | trexp(A.IfExp{cond, first, second}) =
              let val condExp = trexp(cond)
                  val firstExp = trexp(first)
                  val secondExp = trexp(second)
              in (checkInt(condExp); unify(firstExp, secondExp);
                  firstExp)
              end
          | trexp(A.IsNilExp(exp)) = T.App(T.Int, [])
        and trvar(A.SimpleVar id) = 
            (case S.look(venv, id) of
              SOME(ty) => ty
            | NONE => (print ("-------------undefined variable" ^ S.name id);
                     T.Nil))
          | trvar(A.FieldVar(var, symbol)) =
              (case expand(trvar(var)) of T.App(T.Record(fields), typs) => 
                let 
                  val zip = zip(fields, typs)
                  val found = List.find (fn x => #1 x = symbol) zip
                in case found of NONE => (print ("-------------undefined record field name");
                                        T.Nil)
                    | SOME((a,b)) => b
                end
              | _ => (print("record type required"); T.Nil))
          | trvar(A.SubscriptVar(var, exp)) =
              let val arr = trvar(var)
                  val subscript = trexp(exp)
                in checkInt(subscript); 
                   case arr of T.App(T.Array, [ty])=> ty
                        |  _ => (print "-----------------array required\n"; T.Nil)
              end
    in trexp
    end
  and transdec(venv, tenv, A.TypeDec(typedecs)) = (*fix mutual recursion*)
        foldr (fn (dec, {venv, tenv}) => tydec(venv, tenv, dec)) {venv=venv, tenv=tenv} typedecs
  | transdec(venv, tenv, A.FunctionDec(funcdecs)) =
        let
          fun func_header({name, tyvars, param, result, ...}: A.fundec, venv) = 
            let
              val tyv = newtyvarlist(length(tyvars))
              val trans_tyv = map (fn x => E.TyEntry{ty=T.Var(x)}) tyv
              val tenv' = subst_tenv(tenv, tyvars, trans_tyv)
              val t1' = transty(tenv', #typ param)
              val t2' = transty(tenv', result)
            in
              S.enter(venv, name, T.Poly(tyv, T.App(T.Arrow, [t1', t2'])))
            end
          val venv' = foldr func_header venv funcdecs
          fun type_check({name, tyvars, param, result, body, ...}: A.fundec) =
            let
              val SOME(T.Poly(tyv, T.App(T.Arrow, [t1', t2']))) = S.look(venv', name)
              val venv'' = S.enter(venv', #name param, t1')
              val trans_tyv = map (fn x => E.TyEntry{ty=T.Var(x)}) tyv
              val tenv' = subst_tenv(tenv, tyvars, trans_tyv)
              val t3' = transExp(venv'', tenv')(body)
            in
              unify(t2', t3')
            end
        in
          {tenv=tenv,
          venv=venv'}
        end
  |    transdec(venv, tenv, A.VarDec{name, typ, init=A.NilExp, escape}) = 
        let val ty = transty(tenv, typ)
          in {tenv=tenv,
             venv=S.enter(venv, name, ty)}
        end
  |   transdec(venv, tenv, A.VarDec{name, typ, init, escape}) = 
        let
          val t = transty(tenv, typ)
        in
          (unify(t, transExp(venv, tenv)(init)); 
          {tenv=tenv,
          venv=S.enter(venv, name, t)})
        end

  and tydec(venv, tenv, A.ArrayDec(name, tyvars, ty)) =
        let
          val unique = ref(())
          val tyv = newtyvarlist(length(tyvars))
          val trans_tyv = map (fn x => E.TyEntry{ty=T.Var(x)}) tyv
          val tyc = T.TyFun(tyv, T.App(T.Array, [transty(subst_tenv(tenv, tyvars, trans_tyv), ty)]))
        in
          {venv=venv,
          tenv=S.enter(tenv, name, E.TyConEntry{tycon=T.Unique(ref(SOME(tyc)), unique)})}
        end
  |   tydec(venv, tenv, A.RecordDec(name, tyvars, fields)) =
        let
          val unique = ref(())
          val tyv = newtyvarlist(length(tyvars))
          val trans_tyv = map (fn x => E.TyEntry{ty=T.Var(x)}) tyv
          val record_fields = map (fn x => #name x) fields
          val tenv' = S.enter(tenv, name, E.TyConEntry{tycon=T.Unique(ref(NONE), unique)})
          val tenv'' = subst_tenv(tenv', tyvars, trans_tyv)
          val tys = map (fn x => transty(tenv'', #typ x)) fields
          val tyc = T.TyFun(tyv, T.App(T.Record(record_fields), tys))
          val tenv' = S.enter(tenv, name, E.TyConEntry{tycon=T.Unique(ref(SOME(tyc)), unique)})
          fun subst(tenv', T.App(T.Unique(tyc, unique), tys)) =
                (case !tyc of NONE => 
                  let
                    val SOME(E.TyConEntry{tycon}) = S.look(tenv', name)
                    val T.Unique(ref(SOME(tycon)), unique) = tycon
                  in
                    tyc := SOME(tycon); ()
                  end
                | _ => ())
            | subst(tenv', ty) = ()
        in
          (map (fn x => subst(tenv', x)) tys;
          {venv=venv,
          tenv=tenv'})
        end
  |   tydec(venv, tenv, A.ParametricDec(name, tyvars, ty)) =
        let
          val tyv = newtyvarlist(length(tyvars))
          val trans_tyv = map (fn x => E.TyEntry{ty=T.Var(x)}) tyv
          val tenv' = subst_tenv(tenv, tyvars, trans_tyv)
        in
          {venv=venv,
          tenv=S.enter(tenv, name, E.TyConEntry{tycon=T.TyFun(tyv, transty(tenv', ty))})}
        end
  and transty(tenv, A.NameTy(id)) =
        let val SOME(ty) = S.look(tenv, id)
        in case ty of E.TyEntry{ty} => ty (* type variable *)
          | E.TyConEntry{tycon} => (
              case tycon of T.Int => T.App(tycon, [])
              | T.String => T.App(tycon, [])
              | T.Unit => T.App(tycon, [])
          )
        end
  |   transty(tenv, A.FuncTy(formal, result)) = T.App(T.Arrow, [transty(tenv, formal), transty(tenv, result)])
  |   transty(tenv, A.PolyTy(tyvars, ty)) = 
        let
          val tyv = newtyvarlist(length(tyvars))
          val trans_tyv = map (fn x => E.TyEntry{ty=T.Var(x)}) tyv
          val tenv' = subst_tenv(tenv, tyvars, trans_tyv)
        in
          T.Poly(tyv, transty(tenv', ty))
        end
  |   transty(tenv, A.TyCon(symbol, tyargs)) = 
        let
          val SOME(E.TyConEntry{tycon}) = S.look(tenv, symbol)
          val tyargs' = map (fn x => transty(tenv, x)) tyargs
        in
          T.App(tycon, tyargs')
        end
end