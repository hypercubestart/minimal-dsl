use "interpreter.sml";

val run = Interpreter.interpret;

(* datatype peano = z | s of peano *)

let
  fun to_peano(i) = if i > 0 then A.ConstructorExp{con=S.symbol "s", args = [to_peano(i - 1)]}
                    else A.ConstructorExp{con=S.symbol "z", args=[]}

  val exp = A.LetExp{
    decs=[
      A.TypeDec[
        A.ADTDec(
          S.symbol "peano",
          [],
          [
            (S.symbol "z", []),
            (S.symbol "s", [A.TyCon(S.symbol "peano", [])])
          ]
        )
      ]
    ],
    body = to_peano(10)
  }
in
  run(exp)
end;