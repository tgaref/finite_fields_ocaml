(* aux.ml - Polynomial Arithmetic over Fp[x] *)

open Core

module Make (Base : Field_intf.BASE_FIELD) = struct
  module Arith = Arith.Make (Base)

  type base_field = Base.t

  let numbits x =
    let rec helper x acc =
      if Base.equal x Base.zero then acc
      else helper (Base.shift_right x 1) (acc + 1)
    in
    helper x 0

  let deg v = Array.length v - 1

  let lc v =
    if Array.length v = 0 then Base.zero
    else v.(Array.length v - 1)

  let drop_last v =
    let rec find_last idx =
      if idx < 0 then -1
      else if not (Base.equal v.(idx) Base.zero) then idx
      else find_last (idx - 1)
    in
    let last = find_last (Array.length v - 1) in
    if last = -1 then [||]
    else Array.sub v ~pos:0 ~len:(last + 1)

  let extended_gcd a b =
    let rec helper a b =
      if Base.equal b Base.zero then (a, Base.one, Base.zero)
      else
        let open Base in
        let q = a / b in
        let r = a % b in
        let g, s, t = helper b r in
        (g, t, s - (q * t))
    in
    helper a b

  let inv a p =
    if Base.equal a Base.zero then failwith "inv: zero element..."
    else
      let g, s, _ = extended_gcd a p in
      if Base.equal g Base.one then Base.(s % p)
      else failwith "inv: element not coprime..."

  let add as_ bs p =
    let len_a = Array.length as_ in
    let len_b = Array.length bs in
    if len_a >= len_b then
      let res = Array.init len_a ~f:(fun i ->
        if i < len_b then
          Base.((as_.(i) + bs.(i)) % p)
        else
          as_.(i)
      ) in
      drop_last res
    else
      let res = Array.init len_b ~f:(fun i ->
        if i < len_a then
          Base.((as_.(i) + bs.(i)) % p)
        else
          bs.(i)
      ) in
      drop_last res

  let linear_comb as_ bs c p =
    let len_a = Array.length as_ in
    let len_b = Array.length bs in
    if len_a >= len_b then
      Array.init len_a ~f:(fun i ->
        if i < len_b then
          Base.((as_.(i) + (c * bs.(i))) % p)
        else
          as_.(i)
      )
    else
      Array.init len_b ~f:(fun i ->
        if i < len_a then
          Base.((as_.(i) + (c * bs.(i))) % p)
        else
          Base.((c * bs.(i)) % p)
      )

  let scalar_mult c xs p =
    if Base.equal c Base.zero then [||]
    else Array.map xs ~f:(fun x -> Base.((c * x) % p))

  let neg as_ p =
    Array.map as_ ~f:(fun x -> Base.((~- x) % p))

  let mult_poly as_ bs p =
    let n = Array.length as_ in
    let m = Array.length bs in
    if n = 0 || m = 0 then [||]
    else
      let len = n + m - 1 in
      let res = Array.init len ~f:(fun k ->
        let start = max 0 (k - m + 1) in
        let end_ = min k (n - 1) in
        let rec sum_coeffs i acc =
          if i > end_ then acc
          else
            let idx = k - i in
            let term = Base.(as_.(i) * bs.(idx)) in
            sum_coeffs (i + 1) (Base.((acc + term) % p))
        in
        sum_coeffs start Base.zero
      ) in
      drop_last res

  let quo_rem as_ bs p =
    let n = Array.length as_ in
    let m = Array.length bs in
    if m = 0 then failwith "quo_rem: Division by zero element..."
    else if n = 0 then ([||], [||])
    else if n < m then ([||], as_)
    else
      let q_deg = n - m in
      let q = Array.create ~len:(q_deg + 1) Base.zero in
      let r = Array.copy as_ in
      let divisor_lc = bs.(m - 1) in
      let c = inv divisor_lc p in
      for i = q_deg downto 0 do
        let rem_lc = r.(i + m - 1) in
        let q_coeff = Base.((rem_lc * c) % p) in
        q.(i) <- q_coeff;
        if not (Base.equal q_coeff Base.zero) then
          for j = 0 to m - 1 do
            let idx = i + j in
            let sub_val = Base.((q_coeff * bs.(j)) % p) in
            r.(idx) <- Base.((r.(idx) - sub_val) % p)
          done
      done;
      (drop_last q, drop_last r)

  let quo f g p = fst (quo_rem f g p)
  let remdr f g p = snd (quo_rem f g p)

  let mult as_ bs g p =
    let prod = mult_poly as_ bs p in
    remdr prod g p

  let rec gcd_help f g p (s, s') =
    if Array.length f = 0 && Array.length g = 0 then
      failwith "exgcd: both polynomials are zero..."
    else if Array.length g = 0 then (f, s)
    else
      let q, r = quo_rem f g p in
      let s'' = add s (neg (mult_poly s' q p) p) p in
      gcd_help g r p (s', s'')

  let exgcd f g p =
    let deg_f = deg f in
    let deg_g = deg g in
    if deg_f < deg_g then
      let d, t = gcd_help g f p ([|Base.one|], [||]) in
      let s = quo (add d (neg (mult_poly t g p) p) p) f p in
      let c = inv (lc d) p in
      (scalar_mult c d p, scalar_mult c s p, scalar_mult c t p)
    else
      let d, s = gcd_help f g p ([|Base.one|], [||]) in
      let t = quo (add d (neg (mult_poly s g p) p) p) f p in
      let c = inv (lc d) p in
      (scalar_mult c d p, scalar_mult c s p, scalar_mult c t p)

  let power_mod f n g p =
    let rec helper f acc n =
      if Base.equal n Base.zero then acc
      else if Base.equal n Base.one then mult f acc g p
      else
        let open Base in
        let n', r = (n / (of_int 2), n % (of_int 2)) in
        let f' = mult f f g p in
        if equal r one then
          helper f' (mult f acc g p) n'
        else
          helper f' acc n'
    in
    helper f [|Base.one|] n

  let irreduc f p =
    let len = Array.length f in
    if len = 0 then false
    else if len = 1 then false
    else if len = 2 then true
    else
      let x = [|Base.zero; Base.one|] in
      let x' = neg x p in
      let d = len - 1 in
      let bound = d / 2 + 1 in
      let rec helper h n =
        if n >= bound then true
        else
          let g, _, _ = exgcd f (add h x' p) p in
          if Array.length g = 1 && Base.equal g.(0) Base.one then
            helper (power_mod h p f p) (n + 1)
          else
            false
      in
      helper (power_mod x p f p) 1

  let next_list v p =
    let n = Array.length v in
    let mv = Array.create ~len:(n + 1) Base.zero in
    Array.blit ~src:v ~src_pos:0 ~dst:mv ~dst_pos:0 ~len:n;
    let rec loop i carry =
      if i >= n then
        if carry = 1 then (
          mv.(n) <- Base.one;
          n + 1
        ) else
          n
      else
        let val_ = mv.(i) in
        let new_val = Base.(val_ + (of_int carry)) in
        if Base.compare new_val p < 0 then (
          mv.(i) <- new_val;
          n
        ) else (
          mv.(i) <- Base.zero;
          loop (i + 1) 1
        )
    in
    let len = loop 0 1 in
    Array.sub mv ~pos:0 ~len

  let rand_z state p =
    if Base.compare p Base.zero <= 0 then Base.zero
    else
      let loop () =
        let res = ref Base.zero in
        let bits_needed = numbits p in
        let current_bits = ref 0 in
        while !current_bits < bits_needed do
          let r = Base.of_int (Random.State.bits state) in
          res := Base.bit_or (Base.shift_left !res 30) r;
          current_bits := !current_bits + 30
        done;
        let r_mod = Base.(!res % p) in
        r_mod
      in
      loop ()

  let rand_z_range state low high =
    let diff = Base.((high - low) + one) in
    Base.(low + (rand_z state diff))

  let rand_sparse n k p state =
    let a = rand_z_range state Base.one (Base.(p - one)) in
    let v = Array.init k ~f:(fun _ -> rand_z state p) in
    let v' = Array.create ~len:(n - k - 1) Base.zero in
    let poly = Array.concat [ [|a|]; v; v'; [|Base.one|] ] in
    poly

  let find_rand_irred n k p =
    let state = Random.State.make [|759403021|] in
    let rec check () =
      let v = rand_sparse n k p state in
      if irreduc v p then v
      else check ()
    in
    check ()

  let find_sparse_irred n p =
    let rec helper v =
      let padding = Array.create ~len:(n - Array.length v) Base.zero in
      let poly = Array.concat [ v; padding; [|Base.one|] ] in
      if irreduc poly p then poly
      else
        let new_v = next_list v p in
        if Array.length new_v > 0 && Base.equal new_v.(0) Base.zero then
          helper (next_list new_v p)
        else
          helper new_v
    in
    helper [|Base.one|]
end

include Make (Field_intf.Bigint_scalar)
