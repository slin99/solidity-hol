signature solidityLinkLib =
sig
  val address : IntInf.int -> IntInf.int
  val libraries : JSON.value -> (string * string * IntInf.int) list
  val settings : JSON.value -> JSON.value
end
