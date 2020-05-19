use "ast.sml";

structure Semant =
struct
  structure A = AbSyntax
  structure S = Symbol
  structure E = Env
  structure T = Types

  type ty = T.ty
  type venv = Env.enventry Symbol.table
  type tenv = Env.tenventry Symbol.table

  type tyvar = T.tyvar
  type subst_map_type = ty IntBinaryMap.map

  val nexttyvar = ref 0

  fun checkInt(ty) = case ty of T.App(T.Int, []) => ()
                        |  _ => print "-----------------integer required\n";

  fun zip(alist, blist) =
    case alist of a::arest => 
      (case blist of b::brest => (a, b)::(zip(arest, brest))
                |   []       => (print("zip length incorrect"); []))
        |  [] =>
      (case blist of b::brest => (print("zip length incorrect"); [])
                |   []       => [])
  
  fun newtypevar(): tyvar = 
    let val i = !nexttyvar
      in nexttyvar := i + 1; i
    end

  fun newtyvarlist(n) =
    if n > 0 then newtypevar() :: newtyvarlist(n - 1) else []

  fun tyvarTotyArgsMap(tyvars, tyargs) =
    let val tyvarmap: subst_map_type = IntBinaryMap.empty
        val tyvarargs = zip(tyvars, tyargs)
        fun folder((tyv, tya), tyvarmap) = IntBinaryMap.insert(tyvarmap, tyv, tya)
      in foldr folder tyvarmap tyvarargs
    end
      
  fun subst(T.Var(tyvar), sub_map: subst_map_type) = 
    let val ty = IntBinaryMap.find(sub_map, tyvar)
      in case ty of SOME(ty) => ty
                |   NONE => T.Var(tyvar)
    end
    | subst(T.Nil, sub_map: subst_map_type) = T.Nil
    | subst(T.App(T.TyFun(tyvars, ty), tyargs), sub_map: subst_map_type) = 
      let 
          val tyvarmap' = tyvarTotyArgsMap(tyvars, tyargs)
        in subst(subst(ty, tyvarmap'), sub_map)
      end
    | subst(T.App(tycon, tyargs), sub_map: subst_map_type) =
      let fun mapper(ty) = subst(ty, sub_map)
        in T.App(tycon, map mapper tyargs)
      end
    | subst(T.Poly(tyvars, ty), sub_map: subst_map_type) = 
      let val alpha = newtyvarlist(length(tyvars))
          fun toTyVar(i) = T.Var(i)
          val tyvals = map toTyVar alpha
          val subst_rule = zip(tyvars, tyvals)
          fun folder((key, value), mapping) = IntBinaryMap.insert(mapping, key, value)
          val sub_map' = foldr folder sub_map subst_rule
        in T.Poly(alpha, subst(ty, sub_map'))
      end
  
  

  fun unify(T.App(T.Int, tlist), T.App(T.Int, ulist)) = unifylist(tlist, ulist)
    | unify(T.App(T.String, tlist), T.App(T.String, ulist)) = unifylist(tlist, ulist)
    | unify(T.App(T.Unit, tlist), T.App(T.Unit, ulist)) = unifylist(tlist, ulist)
    | unify(T.App(T.Arrow, tlist), T.App(T.Arrow, ulist)) = unifylist(tlist, ulist)
    | unify(T.App(T.Record(tfieldnames), tlist), T.App(T.Record(ufieldnames), ulist)) = 
        let fun fieldnamecheck(t::tlist, u::ulist) = if t = u then fieldnamecheck(tlist, ulist) else print("field names do not match")
              | fieldnamecheck([], []) = ()
              | fieldnamecheck([], u::ulist) = print("ulist longer")
              | fieldnamecheck(t::tlist, []) = print("tlist longer")
        in fieldnamecheck(tfieldnames, ufieldnames); unifylist(tlist, ulist)
        end
    | unify(T.App(T.TyFun(tyvars, ty), tyargs), u) =
        let val t' = subst(ty, tyvarTotyArgsMap(tyvars, tyargs))
          in unify(t', u)
        end
    | unify(t, T.App(T.TyFun(tyvars, ty), tyargs)) = 
        let val u' = subst(ty, tyvarTotyArgsMap(tyvars, tyargs))
          in unify(t, u')
        end
    | unify(T.App(T.Unique(u, z), t), T.App(T.Unique(u', z'), t')) = 
        if z <> z' then print("not the same record occurrence")
        else unifylist(t, t')
    | unify(T.Poly(a, u), T.Poly(a', u')) =
        let fun toTyVar(i) = T.Var(i)
            val vals = map toTyVar a
            val sub_map = tyvarTotyArgsMap(a', vals)
            val u'' = subst(u', sub_map)
          in unify(u, u'')
        end
    | unify(T.Var(t), T.Var(u)) = if t = u then () else print("not the same typevar")
    | unify(T.Nil, T.App(T.Record(_), _)) = ()
    | unify(T.App(T.Record(_), _), T.Nil) = ()
    | unify(_, _) = print("UNIFY ERROR, OTHER CASE!!")

  and unifylist(tlist, ulist) =
    if length(tlist) = length(ulist)
    then let val zipped = zip(tlist, ulist)
             fun unifyty(t, u) = unify(t, u)
          in map unifyty zipped; ()
          end
    else print("Unification: ty list length don't match")

  fun expand(T.App(T.TyFun(tyvars, ty), tyargs)) =
    let val sub_map = tyvarTotyArgsMap(tyvars, tyargs)
      in expand(subst(ty, sub_map))
    end
    | expand(T.App(T.Unique(tycon, z), tyargs)) = expand(T.App(tycon, tyargs))
    | expand(t) = t

  fun transdec(venv, tenv, A.TypeDec([tydec])) = (*FIX NON-RECURSIVE/SINGLE DECLARATIOIN*)
    (case tydec of A.ParametricTyc(symbol, tyvars, ty) =>
      let val B = newtyvarlist(length(tyvars))
          fun toTyVar(tyvar) = T.Var(tyvar)
          val Bvars = map toTyVar B
          val zip = zip(tyvars, Bvars)
          fun folder((k, v), map) = S.enter(map, k, E.TyEntry{ty=v})
          val tenv' = foldr folder tenv zip
        in {venv=venv, tenv=S.enter(tenv, symbol, E.TyConEntry({tycon= T.TyFun(B, transty(tenv', ty))}))}
      end
    | A.RecordTyDec(symbol, tyvars, tyfields) =>
      let val B = newtyvarlist(length(tyvars))
          fun toTyVar(tyvar) = T.Var(tyvar)
          val Bvars = map toTyVar B
          val zip = zip(tyvars, Bvars)
          fun folder((k, v), map) = S.enter(map, k, E.TyEntry{ty=v})
          val tenv' = foldr folder tenv zip
      in {venv=venv, tenv=S.enter(tenv, symbol, E.TyConEntry{tycon=T.TyFun(B, transty(tenv', A.RecordTy(tyfields)))})}
      end)
  | transdec(venv, tenv, A.FunctionDec([{name, tyvars, param, result, body}])) = (*FIX NON-RECURSIVE/SINGLE DECLARATIOIN*)
    let val B = newtyvarlist(length(tyvars))
        fun toTyVar(tyvar) = T.Var(tyvar)
        val Bvars = map toTyVar B
        val zip = zip(tyvars, Bvars)
        fun folder((k, v), map) = S.enter(map, k, E.TyEntry{ty=v})
        val tenv' = foldr folder tenv zip
        val t1 = transty(tenv', A.NameTy(param))
        val t2 = transty(tenv', A.NameTy(result))
        val venv' = S.enter(venv, name, E.FunEntry{ty=T.Poly(B, T.App(T.Arrow, [t1, t2]))})
        val venv'' = S.enter(venv', param, E.FunEntry{ty=t1})
        val t3 = transExp(venv'', tenv')(body)
    in unify(t2, t3); {tenv=tenv, venv=venv'}
    end
  | transdec(venv, tenv, A.VarDec{name, typ, init}) =
    let val ty = transty(tenv, A.NameTy(typ))
    in unify(ty, transExp(venv, tenv)(init)); 
      {tenv=tenv, venv=S.enter(venv, name, E.VarEntry{ty=ty})}
    end
  and transDecs(venv, tenv, []) = {venv=venv, tenv=tenv}
    | transDecs(venv, tenv, x::xs) = 
        let val {venv=venv', tenv=tenv'} = transdec(venv, tenv, x) 
          in transDecs(venv', tenv', xs)
        end 
    (* | T.RecordTyDec(symbol, tyvars, tyfields) => *)
  and transty(tenv, A.NameTy(id)) =
    let val SOME(ty) = S.look(tenv, id)
    in case ty of E.TyEntry{ty} => ty (* type variable *)
        | E.TyConEntry{tycon} => (
          case tycon of Types.Int => T.App(tycon, [])
          | Types.String => T.App(tycon, [])
          | Types.Unit => T.App(tycon, [])
        )
    end
  | transty(tenv, A.TyCon(id, tyargs)) = 
    let val SOME(E.TyConEntry{tycon}) = S.look(tenv, id)
        fun mapper(tyarg) = transty(tenv, tyarg)
    in T.App(tycon, map mapper tyargs)
    end
  | transty(tenv, A.PolyTy(tyvars, ty)) =
    let val B = newtyvarlist(length(tyvars))
        fun mapper(b) = E.TyEntry{ty=T.Var(b)}
        val Bvars = map mapper B
        val zipped = zip(tyvars, Bvars)
        fun insert((k, v), map) = S.enter(map, k, v)
        val tenv' = foldr insert tenv zipped
    in T.Poly(B, transty(tenv', ty))
    end
  | transty(tenv, A.RecordTy(tyfields)) = 
    let val symbollist = map #1 tyfields
        fun trans(symbol, ty) = transty(tenv, ty)
        val typelist = map trans tyfields
    in T.App(T.Record(symbollist), typelist)
    end
  and transExp(venv, tenv) = 
    let fun trexp(A.VarExp(var)) = trvar(var)
        | trexp(A.NilExp) = T.Nil
        | trexp(A.IntExp(i)) = T.App(T.Int, [])
        | trexp(A.StringExp(s)) = T.App(T.String, [])
        | trexp(A.CallExp{func, tyargs, arg}) = (
          let val SOME(E.FunEntry{ty}) = S.look(venv, func)
              val T.Poly(tyvs, T.App(T.Arrow, [t1, t2])) = ty
              fun mapper(tyarg) = transty(tenv, tyarg)
              val tyargs' = map mapper tyargs
              val arg' = trexp(arg)
          in  unify(arg', subst(t1, tyvarTotyArgsMap(tyvs, tyargs')));
              subst(t2, tyvarTotyArgsMap(tyvs, tyargs'))
          end
        )
        | trexp(A.OpExp{left, oper, right}) =
          (checkInt(trexp left);
          checkInt(trexp right);
          T.App(T.Int, []))
        | trexp(A.RecordExp{typ, tyargs, fields}) =
          let val SOME(E.TyConEntry{tycon}) = S.look(tenv, typ)
              fun mapper(tyarg) = transty(tenv, tyarg)
              val tyargs' = map mapper tyargs
              val tr = T.App(tycon, tyargs')
              val T.App(T.Record(fieldnames), expty) = expand(tr)
              val zipped = zip(fields, expty)
              fun unifyfieldlist((_, exp), expty) = unify(trexp(exp), expty)
          in map unifyfieldlist zipped; tr
          end
        | trexp(A.SeqExp exp_list) =
          let fun trSeqExp(exp_list) = 
            (case exp_list of [] => (print "SeqExp empty"; T.Nil)
            |  x::[] => trexp(x)
            |  x::xs => (trexp(x); trSeqExp(xs)))
          in trSeqExp(exp_list)
          end
        | trexp(A.AssignExp{var, exp}) = (
          case var of A.SimpleVar(symbol) =>
            let val ty = trvar(var)
            in unify(ty, trexp(exp)); ty
            end
          | A.FieldVar(recordvar, field: Symbol.symbol) =>
            let val ty = trvar(recordvar)
                val T.App(T.Record(symbols), tys) = ty
                val zipped = zip(symbols, tys)
                fun filterEqual(field_name, ty) = field = field_name
                val filtered = List.filter filterEqual zipped
            in  case filtered of [] => (print ("-------------undefined record field name"); Types.Nil)
                | x::[] => (unify(#2 x, trexp(exp)); #2 x)
            end)
        | trexp(A.LetExp{decs, body}) = 
            let val {venv=venv', tenv=tenv'} = transDecs(venv,tenv,decs)
              in transExp(venv',tenv') body
            end

        and trvar(A.SimpleVar id) = 
          (case S.look(venv, id) of SOME(E.VarEntry{ty}) => ty
          | NONE => (print ("-------------undefined variable" ^ S.name id); Types.Nil))
        | trvar(A.FieldVar(var, symbol)) =
          let val ty = expand(trvar(var))
          in case ty of T.App(T.Record(symbols), tys) => 
                let val zipped = zip(symbols, tys)
                    fun filterEqual(field_name, ty) = symbol = field_name
                    val filtered = List.filter filterEqual zipped
                  in case filtered of [] => (print ("-------------undefined record field name"); Types.Nil)
                                |  x::[] => #2 x
                end
              | _ => (print("record type required"); Types.Nil)
          end 
    in trexp
    end
end