module type BASE_FIELD = sig
  type t
  val zero : t
  val one : t
  val of_int : int -> t
  val to_int_exn : t -> int
  val to_string : t -> string
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val ( % ) : t -> t -> t
  val ( ~- ) : t -> t
  val pow : t -> t -> t
  val bit_or : t -> t -> t
  val bit_and : t -> t -> t
  val bit_xor : t -> t -> t
  val shift_left : t -> int -> t
  val shift_right : t -> int -> t
  val probab_prime : t -> int -> int
  val powm : t -> t -> t -> t
end

module type FINITE_FIELD = sig
  type t
  type element
  type base_field
  val char : t -> base_field
  val degree : t -> int
  val size : t -> base_field
  val zero : t -> element
  val one : t -> element
  val add : element -> element -> element
  val sub : element -> element -> element
  val mul : element -> element -> element
  val neg : element -> element
  val inv : element -> element
  val div : element -> element -> element
  val pow : element -> base_field -> element
  val scalar_mul : base_field -> element -> element
  val is_zero : element -> bool
  val is_one : element -> bool
  val order : element -> base_field
  val show : element -> string
  val equal : element -> element -> bool
  val ( + ) : element -> element -> element
  val ( - ) : element -> element -> element
  val ( * ) : element -> element -> element
  val ( / ) : element -> element -> element
  val ( ~- ) : element -> element

  module O : sig
    val ( + ) : element -> element -> element
    val ( - ) : element -> element -> element
    val ( * ) : element -> element -> element
    val ( / ) : element -> element -> element
    val ( ~- ) : element -> element
  end
end

module type PRIME_FIELD = sig
  include FINITE_FIELD
  val create : base_field -> t
  val element : t -> base_field -> element
end

module type EXTENSION_FIELD = sig
  include FINITE_FIELD
  val create : base_field -> base_field array -> string -> t
  val element : t -> base_field array -> element
  val gen : t -> element
  val basis : t -> element list
end

module Bigint_scalar : BASE_FIELD with type t = Bigint.t = struct
  type t = Bigint.t
  let zero = Bigint.zero
  let one = Bigint.one
  let of_int = Bigint.of_int
  let to_int_exn = Bigint.to_int_exn
  let to_string = Bigint.to_string
  let equal a b = Bigint.equal a b
  let compare a b = Bigint.compare a b
  let ( + ) a b = Bigint.O.(a + b)
  let ( - ) a b = Bigint.O.(a - b)
  let ( * ) a b = Bigint.O.(a * b)
  let ( / ) a b = Bigint.O.(a / b)
  let ( % ) a b = Bigint.O.(a % b)
  let ( ~- ) a = Bigint.O.(~- a)
  let pow a b = Bigint.pow a b
  let bit_or a b = Bigint.bit_or a b
  let bit_and a b = Bigint.bit_and a b
  let bit_xor a b = Bigint.bit_xor a b
  let shift_left a b = Bigint.shift_left a b
  let shift_right a b = Bigint.shift_right a b
  let probab_prime p w = Z.probab_prime (Bigint.to_zarith_bigint p) w
  let powm base exp modulo =
    let z_base = Bigint.to_zarith_bigint base in
    let z_exp = Bigint.to_zarith_bigint exp in
    let z_mod = Bigint.to_zarith_bigint modulo in
    Bigint.of_zarith_bigint (Z.powm z_base z_exp z_mod)
end

module Int_scalar : BASE_FIELD with type t = int = struct
  type t = int
  let zero = 0
  let one = 1
  let of_int x = x
  let to_int_exn x = x
  let to_string = string_of_int
  let equal = ( = )
  let compare = Stdlib.compare
  let ( + ) = ( + )
  let ( - ) = ( - )
  let ( * ) = ( * )
  let ( / ) = ( / )
  let ( % ) a b =
    let r = a mod b in
    if r < 0 then r + b else r
  let ( ~- ) = ( ~- )
  let pow base exp =
    let rec exp_by_sq acc b e =
      if e <= 0 then acc
      else if e mod 2 = 1 then exp_by_sq (acc * b) (b * b) (e / 2)
      else exp_by_sq acc (b * b) (e / 2)
    in
    exp_by_sq 1 base exp
  let bit_or = ( lor )
  let bit_and = ( land )
  let bit_xor = ( lxor )
  let shift_left = ( lsl )
  let shift_right = ( lsr )
  let probab_prime p w = Z.probab_prime (Z.of_int p) w
  let powm base exp modulo =
    let rec loop acc b e =
      if e <= 0 then acc
      else
        let new_acc = if e mod 2 = 1 then (acc * b) mod modulo else acc in
        loop new_acc ((b * b) mod modulo) (e / 2)
    in
    loop 1 (base mod modulo) exp
end


