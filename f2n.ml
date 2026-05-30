(* f2n.ml - Carryless GF(2^n) Arithmetic *)

open Core

module Make (Base : Field_intf.BASE_FIELD) = struct
  let numbits x =
    let rec helper x acc =
      if Base.(equal x zero) then acc
      else helper (Base.shift_right x 1) (acc + 1)
    in
    helper x 0

  let testbit x n =
    let open Base in
    not (equal (bit_and x (shift_left one n)) zero)

  let from_list lst =
    List.fold_right lst ~init:Base.zero ~f:(fun a acc ->
      let open Base in
      if Base.equal a Base.zero then (Base.of_int 2) * acc
      else ((Base.of_int 2) * acc) + Base.one
    )

  let to_list n =
    let rec helper n acc =
      if Base.equal n Base.zero then acc
      else
        let open Base in
        let n', r = (n / (Base.of_int 2), n % (Base.of_int 2)) in
        helper n' (r :: acc)
    in
    let res = helper n [] in
    List.rev res

  let add a b = Base.bit_xor a b

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
end

module F2N_Bigint = Make (Field_intf.Bigint_scalar)

module F2N_Int = Make (Field_intf.Int_scalar)
