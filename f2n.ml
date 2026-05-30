(* f2n.ml - Carryless GF(2^n) Arithmetic *)

open Core

module Make (Base : Field_intf.BASE_FIELD) = struct
  module Arith = Arith.Make (Base)

  type base_field = Base.t
  type t = {
    def_poly : Base.t;
    root_name : string;
  }
  type element = {
    field : t;
    value : Base.t;
  }

  let numbits x =
    let rec helper x acc =
      if Base.(equal x zero) then acc
      else helper (Base.shift_right x 1) (acc + 1)
    in
    helper x 0

  let testbit x n =
    let open Base in
    not (equal (bit_and x (shift_left one n)) zero)


  let mult_no_mod a b =
    let rec helper acc shifted_a current_b =
      if Base.equal current_b Base.zero then acc
      else
        let next_acc =
          if testbit current_b 0 then Base.bit_xor acc shifted_a
          else acc
        in
        helper next_acc (Base.shift_left shifted_a 1) (Base.shift_right current_b 1)
    in
    helper Base.zero a b

  let remdr a m =
    if Base.equal m Base.zero then failwith "remdr: division by zero element..."
    else if Base.equal a Base.zero then Base.zero
    else
      let bits_m = numbits m in
      let rec helper n =
        let diff = numbits n - bits_m in
        if diff < 0 then n
        else
          let term = Base.shift_left m diff in
          helper (Base.bit_xor n term)
      in
      helper a

  let mult a b n =
    if Base.equal b Base.zero then Base.zero
    else remdr (mult_no_mod a b) n

  let power f n g =
    let rec helper f acc n =
      if Base.equal n Base.zero then acc
      else if Base.equal n Base.one then mult f acc g
      else
        let open Base in
        let n', r = (n / (Base.of_int 2), n % (Base.of_int 2)) in
        let f' = mult f f g in
        if Base.equal r Base.one then
          helper f' (mult f acc g) n'
        else
          helper f' acc n'
    in
    helper f Base.one n

  let quo_rem a m =
    if Base.equal m Base.zero then failwith "quoRem: division by zero element..."
    else if Base.equal a Base.zero then (Base.zero, Base.zero)
    else
      let bits_m = numbits m in
      let rec helper q n =
        let diff = numbits n - bits_m in
        if diff < 0 then (q, n)
        else
          let term = Base.shift_left Base.one diff in
          helper (Base.bit_xor q term) (Base.bit_xor n (Base.shift_left m diff))
      in
      helper Base.zero a

  let rec exgcd a b =
    if Base.equal b Base.zero then (a, Base.one, Base.zero)
    else
      let q, r = quo_rem a b in
      let g, s, t = exgcd b r in
      (g, t, Base.bit_xor s (mult_no_mod q t))

  let inverse a g =
    if Base.equal a Base.zero then failwith "inverse: zero element..."
    else
      let d, s, _ = exgcd a g in
      if Base.equal d Base.one then s
      else failwith "inverse: element not coprime to defining polynomial..."

  let create p poly root =
    if not (Base.equal p (Base.of_int 2)) then
      failwith "f2n: characteristic must be 2..."
    else
      let poly_val = ref Base.zero in
      for i = Array.length poly - 1 downto 0 do
        let open Base in
        if not (equal poly.(i) zero) then
          poly_val := bit_or !poly_val (shift_left one i)
      done;
      let n = numbits !poly_val - 1 in
      if n <= 0 then failwith "f2n: invalid polynomial degree..."
      else
        let limit = Base.shift_left Base.one n in
        let check_limit = Base.shift_right limit 1 in
        let expected = Base.shift_left Base.one (n - 1) in
        if not (Base.equal check_limit expected && Base.compare limit Base.zero > 0) then
          failwith "extField: field size exceeds scalar representation capacity (integer overflow)..."
        else
          { def_poly = !poly_val; root_name = root }

  let element field v =
    let v_val = ref Base.zero in
    for i = Array.length v - 1 downto 0 do
      let open Base in
      if not (equal v.(i) zero) then
        v_val := bit_or !v_val (shift_left one i)
    done;
    let r = remdr !v_val field.def_poly in
    { field; value = r }

  let char _ = Base.of_int 2
  let degree field = numbits field.def_poly - 1
  let size field = Base.shift_left Base.one (degree field)
  let zero field = { field; value = Base.zero }
  let one field = { field; value = Base.one }

  let add x y =
    if not (Base.equal x.field.def_poly y.field.def_poly) then
      failwith "(+): elements belong to different fields..."
    else
      { field = x.field; value = Base.bit_xor x.value y.value }

  let sub = add

  let mul x y =
    if not (Base.equal x.field.def_poly y.field.def_poly) then
      failwith "(*): elements belong to different fields..."
    else
      { field = x.field; value = mult x.value y.value x.field.def_poly }

  let neg x = x

  let inv x =
    if Base.equal x.value Base.zero then failwith "recip: zero element..."
    else { field = x.field; value = inverse x.value x.field.def_poly }

  let div x y = mul x (inv y)

  let rec pow x n =
    if Base.compare n Base.zero < 0 then
      if Base.equal x.value Base.zero then failwith "raise to power: zero element to negative power..."
      else pow (inv x) (Base.(~- n))
    else if Base.equal x.value Base.zero then
      if Base.equal n Base.zero then one x.field
      else zero x.field
    else
      { field = x.field; value = power x.value n x.field.def_poly }

  let scalar_mul n x =
    let is_zero_scalar =
      let open Base in
      equal (n % (of_int 2)) zero
    in
    if is_zero_scalar then zero x.field
    else x

  let is_zero x = Base.equal x.value Base.zero
  let is_one x = Base.equal x.value Base.one

  let show x =
    if Base.equal x.value Base.zero then "0"
    else
      let idfr = x.field.root_name in
      let buf = Buffer.create 16 in
      let deg = numbits x.value - 1 in
      for i = 0 to deg do
        if testbit x.value i then (
          if Buffer.length buf > 0 then Buffer.add_string buf " + ";
          match i with
          | 0 -> Buffer.add_string buf "1"
          | 1 -> Buffer.add_string buf idfr
          | _ -> Buffer.add_string buf (idfr ^ "^" ^ string_of_int i)
        )
      done;
      Buffer.contents buf

  let equal x y =
    Base.equal x.field.def_poly y.field.def_poly && Base.equal x.value y.value

  let basis field =
    let a = { field; value = Base.of_int 2 } in
    let n = degree field in
    let rec helper b i acc =
      if i = 0 then List.rev acc
      else
        let c = mul b a in
        helper c (i - 1) (b :: acc)
    in
    helper (one field) n []

  let order x =
    if is_zero x then failwith "order: zero element..."
    else
      let gf = x.field in
      let m = Base.((shift_left one (degree gf)) - one) in
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
    let g = field.def_poly in
    let n = degree field in
    if n <= 1 then one field
    else
      let m = Base.((shift_left one n) - one) in
      let factors = Arith.factorise m in
      let rec find cand =
        let rec check_factors = function
          | [] -> true
          | (q, _) :: tl ->
              let exp = Base.(m / q) in
              let res = power cand exp g in
              if Base.equal res Base.one then false
              else check_factors tl
        in
        if check_factors factors then { field; value = cand }
        else find (Base.(cand + Base.one))
      in
      find (Base.of_int 2)

  let rand_state = Core.Random.State.make_self_init ()
  let get_rand_elt field =
    let n = degree field in
    let limit = Base.shift_left Base.one n in
    let loop () =
      let res = ref Base.zero in
      let bits_needed = n in
      let current_bits = ref 0 in
      while !current_bits < bits_needed do
        let r = Base.of_int (Core.Random.State.bits rand_state) in
        res := Base.bit_or (Base.shift_left !res 30) r;
        current_bits := !current_bits + 30
      done;
      let mask = Base.(limit - one) in
      Base.bit_and !res mask
    in
    { field; value = loop () }

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

module F2N_Bigint = Make (Field_intf.Bigint_scalar)

module F2N_Int = Make (Field_intf.Int_scalar)
