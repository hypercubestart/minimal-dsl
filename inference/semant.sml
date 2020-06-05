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
    | printType(T.Poly(tyvars, ty)) = print "Poly"
  and printTyCon(T.Int) = print "Int"
    | printTyCon(T.String) = print "String"
    | printTyCon(T.Unit) = print "Unit"
    | printTyCon(T.Arrow) = print "Arrow"
    | printTyCon(T.Array) = print "Array"
    | printTyCon(T.Record(fields)) = print "Record"
    | printTyCon(T.TyFun(tyvs, ty)) = print "TyFun"
    | printTyCon(T.Unique(ref(SOME(tycon)), unique)) = (print "Unique"; printTyCon(tycon))

  fun addMetaEnv([], []) = ()
  |   addMetaEnv(m::mlist, t::tlist) = (HashTable.insert sigma_m (m, t); addMetaEnv(mlist, tlist))

  fun newmetavar() = 
    let val i = !nextmetavar
    in nexttyvar := i + 1; i
    end

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

  and occursin(T.Nil, meta) = true
  |   occursin(T.App(tycon, tylist), meta) = 
        let
          val T.App(tycon', tys') = expand(T.App(tycon, tylist))
        in
          foldl (fn(ty, bool) => bool andalso occursin(ty, meta)) true tys'
        end
  |   occursin(T.Var(tyvar), meta) = true
  |   occursin(T.Meta(tymeta), meta) = tymeta = meta
  |   occursin(T.Poly(tyvars, ty), meta) = occursin(ty, meta)

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
  |   unify(a, b) = (printType(a); printType(b); print("unify failed"); raise TypeCheck)
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
        val dowork = map (fn x => getMetaVars(x, venvMetaVars)) (HashTable.listItems venv)
        val dowork = map (fn x => Helper.removeIfContains(tMetaVars, x)) (HashTable.listItems venvMetaVars)
        val free_vars = HashTable.listItems tMetaVars
        val tyv = newtyvarlist(length(free_vars))
        val tyvars = map (fn x => T.Var(x)) tyv
      in
        (addMetaEnv(free_vars, tyvars); T.Poly(tyv, t))
      end

  and getMetaVars(T.Nil, ht) = ()
  |   getMetaVars(T.App(tycon, tys), ht) = (
        case expand(T.App(tycon, tys)) of T.App(tyc, tys) => (map (fn (x) => getMetaVars(x, ht)) tys; ())
        | ty => getMetaVars(ty, ht)
      )
  |   getMetaVars(T.Var(tyvar), ht) = ()
  |   getMetaVars(T.Meta(tymeta), ht) = (
        case expand(T.Meta(tymeta)) of 
        T.Meta(t) => if tymeta = t then HashTable.insert ht (t,t) else getMetaVars(T.Meta(t), ht)
        | other => getMetaVars(other, ht) 
      )
  |   getMetaVars(T.Poly(tyvars, ty), ht) = getMetaVars(ty, ht)

  fun transdec(venv, tenv, A.FunctionDec[fundec])
end