(* extensionff.mli - Concrete Extension Field Interface *)

module Make (Base : Field_intf.BASE_FIELD) : sig
  include Field_intf.EXTENSION_FIELD with type base_field = Base.t
end

module EF_Bigint : sig
  include Field_intf.EXTENSION_FIELD with type base_field = Bigint.t
end

module EF_Int : sig
  include Field_intf.EXTENSION_FIELD with type base_field = int
end
