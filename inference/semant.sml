use "ast.sml";
use "helper.sml";

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
  val nextmetavar = ref 0

  (* transVar: venv * tenv * AbSyntax.var -> expty
  transExp: venv * tenv * AbSyntax.exp -> expty
  transDec: venv * tenv * AbSyntax.dec -> {venv: venv, tenv: tenv}
  transTy:          tenv * AbSyntax.ty -> Types.ty *)
  structure A = AbSyntax
  structure S = Symbol
  structure E = Env
  structure T = Types

  exception MetaVar
  val sigma_m : (int, T.ty) HashTable.hash_table = HashTable.mkTable(Word.fromInt, op =)(128, MetaVar)

  exception TypeCheck

  fun checkInt(ty) = case ty of T.App(T.Int, []) => ()
                        |  _ => print "-----------------integer required\n";


  fun zip(a::al, b::bl) = (a,b)::zip(al, bl)
  |   zip([], []) = []

  fun printType(T.Nil) = print "Nil"
    | printType(T.App(tycon, tys)) = (print "App"; printTyCon(tycon))
    | printType(T.Var(tyvar)) = print "Var"
    | printType(T.Poly(tyvars, ty)) = (print("Poly" ^ Int.toString(length(tyvars))); printType(ty)) 
    | printType(T.Meta(meta)) = print "Meta"
    | printType(T.Field(record, field)) = (print "Field"; printType(record); printType(field))
  and printTyCon(T.Int) = print "Int"
    | printTyCon(T.String) = print "String"
    | printTyCon(T.Unit) = print "Unit"
    | printTyCon(T.Arrow) = print "Arrow"
    | printTyCon(T.Array) = print "Array"
    | printTyCon(T.Record(fields)) = print "Record"
    | printTyCon(T.TyFun(tyvs, ty)) = (print "TyFun"; printType(ty))
    | printTyCon(T.Unique(ref(SOME(tycon)), unique)) = (print "Unique"; printTyCon(tycon))

  fun addMetaEnv([], []) = ()
  |   addMetaEnv(m::mlist, t::tlist) = (HashTable.insert sigma_m (m, t); addMetaEnv(mlist, tlist))

  fun newmetavar() = 
    let val i = !nextmetavar
    in nextmetavar := i + 1; i
    end

  fun newmetavarlist(n) =
    if n > 0 then newmetavar()::newmetavarlist(n - 1) else []

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
  |   subst(T.Meta(meta), tenv) =
        if Helper.contains(sigma_m, meta) then subst(HashTable.lookup sigma_m meta, tenv)
        else T.Meta(meta)
  |   subst(T.Field(record, field), tenv) = T.Field(subst(record, tenv), subst(field, tenv))

  and occursin(T.Nil, meta) = false
  |   occursin(T.App(tycon, tylist), meta) = 
        let
          val T.App(tycon', tys') = expand(T.App(tycon, tylist))
        in
          false
          (* foldl (fn(ty, bool) => bool orelse occursin(ty, meta)) false tys' *) (*DOESNT HANDLE RECURSIVE RECORDS*)
        end
  |   occursin(T.Var(tyvar), meta) = false
  |   occursin(T.Meta(tymeta), meta) = tymeta = meta
  |   occursin(T.Poly(tyvars, ty), meta) = occursin(ty, meta)
  |   occursin(T.Field(record, field), meta) = occursin(field, meta)

  and unify(T.App(T.Int, tyvars1), T.App(T.Int, tyvars2)) = unifylist(tyvars1, tyvars2)
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
  |   unify(T.Meta(meta), t) =
        if Helper.contains(sigma_m, meta) then unify(HashTable.lookup sigma_m meta, t)
        else if Helper.meta1(t) then unify(T.Meta(meta), expand(t))
        else if Helper.meta2(sigma_m, t) then (
          let
            val T.Meta(b) = t
          in
            unify(T.Meta(meta), HashTable.lookup sigma_m b)
          end
        )
        else if Helper.meta3(meta, t) then ()
        else if occursin(t, meta) then print "meta var cycle"
        else HashTable.insert sigma_m (meta, t)
  |   unify(t, T.Meta(meta)) = unify(T.Meta(meta), t)
  |   unify(T.Field(r1, f1), T.Field(r2, f2)) = (print "xyz";printType(r1); print"\n"; printType(r2); unify(r1, r2); print "doe"; unify(f1, f2))
  |   unify(a, b) = (printType(a); print("\n"); printType(b); print("unify failed"); raise TypeCheck)
  and unifylist(t1::t1list, t2::t2list) = (unify(t1, t2); unifylist(t1list, t2list))
  |   unifylist([], []) = ()

  and expand(T.App(T.TyFun(tyvars, ty), tyargs)) = expand(subst(ty, base_subst_tenv(tyvars, tyargs)))
  |   expand(T.App(T.Unique(tycon, unique), tyargs)) = 
        let
          val SOME(tycon) = !tycon
        in
          expand(T.App(tycon, tyargs))
        end
  |   expand(T.Meta(meta)) =
        if Helper.contains(sigma_m, meta) then expand(HashTable.lookup sigma_m meta)
        else T.Meta(meta)
  |   expand(u) = u

  and generalize(venv, t) =
      let
        val tMetaVars: (int,int) HashTable.hash_table = HashTable.mkTable(Word.fromInt, op=)(128, Fail "not found")
        val venvMetaVars: (int,int) HashTable.hash_table = HashTable.mkTable(Word.fromInt, op=)(128, Fail "not found")
        val dowork = getMetaVars(t, tMetaVars)
        val dowork = map (fn x => getMetaVars(x, venvMetaVars)) (S.listItems venv)
        val dowork = map (fn x => Helper.removeIfContains(tMetaVars, x)) (HashTable.listItems venvMetaVars)
        val free_vars = HashTable.listItems tMetaVars
        val tyv = newtyvarlist(length(free_vars))
        val tyvars = map (fn x => T.Var(x)) tyv
      in
        (addMetaEnv(free_vars, tyvars); print "done"; T.Poly(tyv, t))
      end

  and getMetaVars(T.Nil, ht) = ()
  |   getMetaVars(T.App(tycon, tys), ht) = (*DOESNT HANDLE RECURSIVE RECORDS*)
      (
        case expand(T.App(tycon, tys)) of 
        T.App(T.Record(symbols), tys) => ()
        | T.App(tycon, tys) => (map (fn (x) => getMetaVars(x, ht)) tys; ())
        | ty => getMetaVars(ty, ht)
      )
  |   getMetaVars(T.Var(tyvar), ht) = ()
  |   getMetaVars(T.Meta(tymeta), ht) = (
        case expand(T.Meta(tymeta)) of 
        T.Meta(t) => if tymeta = t then HashTable.insert ht (t,t) else getMetaVars(T.Meta(t), ht)
        | other => getMetaVars(other, ht) 
      )
  |   getMetaVars(T.Poly(tyvars, ty), ht) = getMetaVars(ty, ht)

  and instantiate(T.Poly(tyvars, ty)) = 
    let
      val meta = newmetavarlist(length(tyvars))
      val metavars = map (fn x => T.Meta(x)) meta
      val base_tenv = base_subst_tenv(tyvars, metavars)
    in
      subst(ty, base_tenv)
    end
  |   instantiate(x) = x

  fun transExp(venv: venv, tenv) = 
    let fun trexp(A.VarExp(var)) = trvar(var)
          | trexp(A.NilExp) = T.Nil
          | trexp(A.IntExp int) = T.App(T.Int, [])
          | trexp(A.StringExp str) = T.App(T.String, [])
          | trexp(A.CallExp{func, args}) = 
              let
                val functype = trexp(func)
                val a = (printType(functype); print("\nabc\n"))
                val formal = trexp(args)
                val result = T.Meta(newmetavar())
              in
                (unify(functype, T.App(T.Arrow, [formal, result])); result)
              end
          | trexp(A.OpExp{left, oper, right}) =
              let
                val leftty = trexp left
              in
                (unify(leftty, T.App(T.Int, []));
                unify(trexp right, T.App(T.Int, []));
                T.App(T.Int, [])
                )
              end
              (* (unify((trexp left), T.App(T.Int, []));
              unify((trexp right), T.App(T.Int, [])); 
              T.App(T.Int, [])) *)
          | trexp(A.RecordExp{fields, typ}) = 
              let
                val SOME(E.TyConEntry{tycon}) 
                      = S.look(tenv, typ)
                val T.Unique(ref(SOME(T.TyFun(tyvars, ty))), z) = tycon
                val meta = newmetavarlist(length(tyvars))
                val metavars = map (fn x => T.Meta(x)) meta
                val tr' = subst(ty, base_subst_tenv(tyvars, metavars))
                val T.App(T.Record(symbols), fieldtypes) = expand(tr')
                val expfields = map (fn x => trexp(# 2 x)) fields
              in
                (unifylist(fieldtypes, expfields); T.App(tycon, metavars))
              end
          | trexp(A.SeqExp exp_list) =
              let 
                fun trSeqExp(exp_list) = 
                  (case exp_list of [] => (print "SeqExp empty"; T.Nil)
                                 |  x::[] => trexp(x)
                                 |  x::xs => (trexp(x); trSeqExp(xs)))
              in trSeqExp(exp_list)
              end
          | trexp(A.LetExp{decs, body}) = 
              let 
                fun transDec(dec, {venv,tenv}) = transdec(venv, tenv, dec)
                val {venv=venv', tenv=tenv'} = foldl transDec {venv=venv, tenv=tenv} decs
              in transExp(venv',tenv') body
              end
          | trexp(A.IfExp{cond, first, second}) =
              let val condExp = trexp(cond)
                  val firstExp = trexp(first)
                  val secondExp = trexp(second)
              in (unify(condExp, T.App(T.Int, [])); unify(firstExp, secondExp);
                  firstExp)
              end
          | trexp(A.IsNilExp(exp)) = T.App(T.Int, [])
        and trvar(A.SimpleVar id) = 
              let
                val SOME(ty) = S.look(venv, id)
              in
                instantiate(ty)
              end
        |   trvar(A.FieldVar(record, symbol)) =
              let
                val recordTy = trexp(record)
                val b = (printType(expand(recordTy)); print "b\n")
                val meta = T.Meta(newmetavar())
                val SOME(E.TyEntry{ty}) = S.look(tenv, symbol)
                val d = (printType(ty); print "d\n")
                val tfield = instantiate(ty)
                val c = (printType(tfield); print "c\n")
              in
                (unify(tfield, T.Field(recordTy, meta)); print "ahh"; meta)
              end
    in trexp
    end
  and transdec(venv, tenv, A.TypeDec(typedecs)) = (*fix mutual recursion*)
        foldr (fn (dec, {venv, tenv}) => tydec(venv, tenv, dec)) {venv=venv, tenv=tenv} typedecs
  |   transdec(venv, tenv, A.FunctionDec(fundecs)) = 
        let
          val formals = map (fn x => T.Meta(x)) (newmetavarlist(length(fundecs)))
          val results = map (fn x => T.Meta(x)) (newmetavarlist(length(fundecs)))
          val functys = List.tabulate(length(fundecs), 
            (fn x => (List.nth(fundecs, x), List.nth(formals, x), List.nth(results, x)))
          )
          val venv' = foldl (fn((fundec, formal, result), venv) => S.enter(venv, #name fundec, T.App(T.Arrow, [formal, result]))) venv functys
          fun processSingle((fundec: A.fundec, formal, result), venv) =
            let
              val venv'' = S.enter(venv', #param fundec, formal)
              val expty = transExp(venv'', tenv)(#body fundec)
            in
              unify(result, expty);
              S.enter(venv, #name fundec, generalize(venv, T.App(T.Arrow, [formal, result])))
            end
        in
          {tenv=tenv, 
          venv=foldl processSingle venv functys}
        end
  |   transdec(venv, tenv, A.VarDec{name, init, typ=NONE}) =
    (case transExp(venv, tenv)(init) of
    T.Nil => (print("variable declaration with nil not allowed"); {tenv=tenv, venv=venv})
    | ty => {tenv=tenv, 
            venv=S.enter(venv, name, if S.contains(venv, name) then T.Poly([], ty) else generalize(venv, ty))}
    )
  |   transdec(venv, tenv, A.VarDec{name, init=A.NilExp, typ=SOME(ty)}) =
        let val ty = transty(tenv, ty)
        in {tenv=tenv,
           venv=S.enter(venv, name, ty)}
        end

  and tydec(venv, tenv: tenv, A.RecordDec(symbol, tysymbols, fields)) = 
    let
      val unique = ref(())
      val tyv = newtyvarlist(length(tysymbols))
      val tyvars = map (fn x => E.TyEntry{ty=T.Var(x)}) tyv
      val tenv' = S.enter(tenv, symbol, E.TyConEntry{tycon=T.Unique(ref(NONE), unique)})
      val tenv' = subst_tenv(tenv', tysymbols, tyvars)
      val fieldtys = map (fn x => transty(tenv', #typ x)) fields
      val fieldnames = map #name fields
      val recordTycon = T.Unique(ref(SOME(T.TyFun(tyv, T.App(T.Record(fieldnames), fieldtys)))), unique)
      val tenv'' = S.enter(tenv, symbol, E.TyConEntry{tycon=recordTycon})
      val recordTy = T.App(recordTycon, map (fn x => T.Var(x)) tyv)
      val tenv'' = foldl (fn((fname, fty), tenv) => S.enter(tenv, fname, E.TyEntry{ty=T.Poly(tyv, T.Field(recordTy, fty))})) tenv'' (zip(fieldnames, fieldtys))
      fun subst(tenv, T.App(T.Unique(tyc, unique), tys)) =
                (case !tyc of NONE => 
                  let
                    val SOME(E.TyConEntry{tycon}) = S.look(tenv, symbol)
                  in
                    tyc := SOME(tycon); ()
                  end
                | _ => ())
            | subst(tenv, ty) = ()
    in
      (map (fn x => subst(tenv'', x)) fieldtys;
      {venv=venv,
      tenv=tenv''})
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
  |   transty(tenv, A.TyCon(symbol, tyargs)) = 
        let
          val SOME(E.TyConEntry{tycon}) = S.look(tenv, symbol)
          val tyargs' = map (fn x => transty(tenv, x)) tyargs
        in
          T.App(tycon, tyargs')
        end
end