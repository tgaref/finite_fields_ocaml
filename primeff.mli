(* primeff.mli - Concrete Prime Field Interface *)

module Make (Base : Field_intf.BASE_FIELD) : sig
  include Field_intf.PRIME_FIELD with type base_field = Base.t
  val powm : base_field -> base_field -> base_field -> base_field
  val sig_mul : element -> element -> element
end

module PF_Bigint : sig
  include Field_intf.PRIME_FIELD with type base_field = Bigint.t
  val powm : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t
  val sig_mul : element -> element -> element
end

module PF_Int : sig
  include Field_intf.PRIME_FIELD with type base_field = int
  val powm : int -> int -> int -> int
  val sig_mul : element -> element -> element
end
