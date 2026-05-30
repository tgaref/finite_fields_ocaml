(* extensionff.mli - Concrete Extension Field Interface *)

module Make (Base : Field_intf.BASE_FIELD) : sig
  include Field_intf.EXTENSION_FIELD with type base_field = Base.t
  val show_element_list : (base_field -> bool) -> base_field list -> string -> string
end

module EF_Bigint : sig
  include Field_intf.EXTENSION_FIELD with type base_field = Bigint.t
  val show_element_list : (Bigint.t -> bool) -> Bigint.t list -> string -> string
end

module EF_Int : sig
  include Field_intf.EXTENSION_FIELD with type base_field = int
  val show_element_list : (int -> bool) -> int list -> string -> string
end
