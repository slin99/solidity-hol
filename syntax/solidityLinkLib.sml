(* One link assignment for source import, compiler artifacts and test worlds.
 * IDs are compilation-wide, so libraries with the same name in different
 * files still receive distinct addresses. No HOL frontend dependencies. *)
structure solidityLinkLib :> solidityLinkLib =
struct

val field = JSONUtil.lookupField
fun object (JSON.OBJECT xs) = xs
  | object v = raise JSONUtil.JSONError (JSONUtil.NotObject, v)

fun address id = 0x100000 + id : IntInf.int

fun libraries output =
  List.concat (map (fn (source, value) =>
    List.mapPartial (fn node =>
      if JSONUtil.asString (field node "nodeType") = "ContractDefinition" andalso
         JSONUtil.asString (field node "contractKind") = "library"
      then SOME (source, JSONUtil.asString (field node "name"),
                 address (JSONUtil.asIntInf (field node "id")))
      else NONE)
      (JSONUtil.arrayMap (fn x => x) (field (field value "ast") "nodes")))
    (object (field output "sources")))

fun settings output =
  let
    val libs = libraries output
    fun hex n = "0x" ^ StringCvt.padLeft #"0" 40
      (String.map Char.toLower (IntInf.fmt StringCvt.HEX n))
  in
    JSON.OBJECT (List.mapPartial (fn (source, _) =>
      case List.mapPartial (fn (file, name, addr) =>
             if file = source then SOME (name, JSON.STRING (hex addr)) else NONE) libs of
        [] => NONE
      | entries => SOME (source, JSON.OBJECT entries))
      (object (field output "sources")))
  end
end
