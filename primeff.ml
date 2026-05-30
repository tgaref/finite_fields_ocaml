(* primeff.ml - Specialized Prime Field Implementation *)

open Core

module Make (Base : Field_intf.BASE_FIELD) = struct
  module Aux = Aux.Make (Base)
  module Arith = Arith.Make (Base)

  type base_field = Base.t
  type t = { char : Base.t }
  type element = { field : t; value : Base.t }

  let powm base exp modulo = Base.powm base exp modulo

  let create p =
    if Base.probab_prime p 25 = 0 then failwith "primeField: non-prime characteristic..."
    else { char = p }

  let element field v =
    { field; value = Base.(v % field.char) }

  let char field = field.char
  let degree _ = 1
  let size field = field.char
  let zero field = { field; value = Base.zero }
  let one field = { field; value = Base.one }

  let add x y =
    if not (phys_equal x.field y.field) then failwith "(+): elements belong to different fields..."
    else { field = x.field; value = Base.((x.value + y.value) % x.field.char) }

  let sub x y =
    if not (phys_equal x.field y.field) then failwith "(-): elements belong to different fields..."
    else { field = x.field; value = Base.((x.value - y.value) % x.field.char) }

  let sig_mul x y =
    if not (phys_equal x.field y.field) then failwith "(*): elements belong to different fields..."
    else { field = x.field; value = Base.((x.value * y.value) % x.field.char) }

  let mul = sig_mul

  let neg x =
    { field = x.field; value = Base.((~- (x.value)) % x.field.char) }

  let inv x =
    if Base.equal x.value Base.zero then failwith "recip: zero element..."
    else
      let p = x.field.char in
      let _, s, _ = Aux.extended_gcd x.value p in
      { field = x.field; value = Base.(s % p) }

  let div x y =
    if not (phys_equal x.field y.field) then failwith "(/): elements belong to different fields..."
    else mul x (inv y)

  let rec pow x n =
    let p = x.field.char in
    if Base.compare n Base.zero < 0 then
      if Base.equal x.value Base.zero then failwith "raise to power: zero element to negative power..."
      else pow (inv x) (Base.(~- n))
    else if Base.equal x.value Base.zero then { field = x.field; value = Base.zero }
    else { field = x.field; value = powm x.value n p }

  let scalar_mul n x =
    let p = x.field.char in
    { field = x.field; value = Base.((n * x.value) % p) }

  let is_zero x = Base.equal x.value Base.zero
  let is_one x = Base.equal x.value Base.one
  let show x = Base.to_string x.value
  let equal x y = phys_equal x.field y.field && Base.equal x.value y.value

  let order x =
    if is_zero x then failwith "order: zero element..."
    else
      let gf = x.field in
      let m = Base.(gf.char - Base.one) in
      let factor_list = Arith.factorise m in
      let rec check_prime k q ind =
        if is_one (pow x k) then ind
        else check_prime (Base.(k * q)) q (ind + 1)
      in
      Stdlib.List.fold_left (fun acc (q, e) ->
        let p_val_pow_e = Base.pow q (Base.of_int e) in
        let k_init = Base.(m / p_val_pow_e) in
        let ind = check_prime k_init q 0 in
        let term = Base.pow q (Base.of_int ind) in
        Base.(acc * term)
      ) Base.one factor_list

  let get_generator field =
    let p = field.char in
    if Base.equal p (Base.of_int 2) then element field Base.one
    else
      let m = Base.(p - Base.one) in
      let factors = Arith.factorise m in
      let rec find g_val =
        let rec check_factors = function
          | [] -> true
          | (q, _) :: tl ->
              let exp = Base.(m / q) in
              let res = powm g_val exp p in
              if Base.equal res Base.one then false
              else check_factors tl
        in
        if check_factors factors then element field g_val
        else find (Base.(g_val + Base.one))
      in
      find (Base.of_int 2)

  let rand_state = Random.State.make_self_init ()
  let get_rand_elt field =
    element field (Aux.rand_z rand_state field.char)

  let ( + ) = add
  let ( - ) = sub
  let ( * ) = mul
  let ( / ) = div
  let ( ~- ) = neg

  module O = struct
    let ( + ) = add
    let ( - ) = sub
    let ( * ) = mul
    let ( / ) = div
    let ( ~- ) = neg
  end
end

module PF_Bigint = Make (Field_intf.Bigint_scalar)

module PF_Int = Make (Field_intf.Int_scalar)
