(* extensionff.ml - Specialized Extension Field Implementation *)

module Make (Base : Field_intf.BASE_FIELD) = struct
  module Aux = Aux.Make (Base)
  module Arith = Arith.Make (Base)

  type base_field = Base.t
  type t = {
    char : Base.t;
    def_poly : Base.t array;
    root_name : string;
  }
  type element = { field : t; values : Base.t array }

  let create p poly root =
    if Base.probab_prime p 25 = 0 then failwith "extField: non-prime characteristic..."
    else
      let poly_mod = Array.map (fun x -> Base.(x % p)) poly in
      let poly' = Aux.drop_last poly_mod in
      if not (Aux.irreduc poly' p) then failwith "extField: non-irreducible polynomial..."
      else { char = p; def_poly = poly'; root_name = root }

  let element field v =
    let p = field.char in
    let poly = field.def_poly in
    let v_mod = Array.map (fun x -> Base.(x % p)) v in
    let v1 = Aux.drop_last v_mod in
    let _, r = Aux.quo_rem v1 poly p in
    { field; values = r }

  let char field = field.char
  let degree field = Array.length field.def_poly
  let size field = Base.pow field.char (Base.of_int (Array.length field.def_poly))
  let zero field = { field; values = [||] }
  let one field = { field; values = [|Base.one|] }
  let gen field = { field; values = [|Base.zero; Base.one|] }

  let add x y =
    if x.field <> y.field then failwith "(+): elements belong to different fields..."
    else { field = x.field; values = Aux.add x.values y.values x.field.char }

  let sub x y =
    if x.field <> y.field then failwith "(-): elements belong to different fields..."
    else
      let p = x.field.char in
      { field = x.field; values = Aux.add x.values (Aux.neg y.values p) p }

  let mul x y =
    if x.field <> y.field then failwith "(*): elements belong to different fields..."
    else { field = x.field; values = Aux.mult x.values y.values x.field.def_poly x.field.char }

  let neg x =
    { field = x.field; values = Aux.neg x.values x.field.char }

  let inv x =
    if Array.length x.values = 0 then failwith "recip: zero element..."
    else
      let p = x.field.char in
      let poly = x.field.def_poly in
      let _, s, _ = Aux.exgcd x.values poly p in
      { field = x.field; values = s }

  let div x y =
    if x.field <> y.field then failwith "(/): elements belong to different fields..."
    else mul x (inv y)

  let rec pow x n =
    let p = x.field.char in
    let poly = x.field.def_poly in
    if Base.compare n Base.zero < 0 then
      if Array.length x.values = 0 then failwith "raise to power: zero element to negative power..."
      else pow (inv x) (Base.(~- n))
    else if Array.length x.values = 0 then { field = x.field; values = [||] }
    else
      let res = Aux.power_mod x.values n poly p in
      { field = x.field; values = res }

  let scalar_mul n x =
    let p = x.field.char in
    if Base.equal (Base.(n % p)) Base.zero then { field = x.field; values = [||] }
    else
      let u = Array.map (fun v -> Base.((n * v) % p)) x.values in
      { field = x.field; values = u }

  let is_zero x = Array.length x.values = 0
  let is_one x = Array.length x.values = 1 && Base.equal x.values.(0) Base.one

  let show_element_list zero_test f idfr =
    match f with
    | [] -> "0"
    | [v] -> Base.to_string v
    | _ ->
      let fold_f (acc, idx) x =
        if zero_test x then (acc, idx + 1)
        else
          let term =
            match idx with
            | 0 -> Base.to_string x ^ " +"
            | 1 -> Base.to_string x ^ "*" ^ idfr ^ " +"
            | _ -> Base.to_string x ^ "*" ^ idfr ^ "^" ^ string_of_int idx ^ " +"
          in
          (acc ^ term, idx + 1)
      in
      let result, _ = List.fold_left fold_f ("", 0) f in
      if String.length result = 0 then "0"
      else
        String.sub result 0 (String.length result - 2)

  let show x =
    show_element_list (Base.equal Base.zero) (Array.to_list x.values) x.field.root_name

  let equal x y =
    let f1 = x.field in
    let f2 = y.field in
    Base.equal f1.char f2.char &&
    Array.length f1.def_poly = Array.length f2.def_poly &&
    let rec check_poly i =
      if i < 0 then true
      else if not (Base.equal f1.def_poly.(i) f2.def_poly.(i)) then false
      else check_poly (i - 1)
    in
    check_poly (Array.length f1.def_poly - 1) &&
    String.equal f1.root_name f2.root_name &&
    Array.length x.values = Array.length y.values &&
    let rec check_vals i =
      if i < 0 then true
      else if not (Base.equal x.values.(i) y.values.(i)) then false
      else check_vals (i - 1)
    in
    check_vals (Array.length x.values - 1)

  let basis field =
    let a = gen field in
    let n = Array.length field.def_poly in
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
      let m = Base.(pow gf.char (of_int (Array.length gf.def_poly)) - one) in
      let factor_list = Arith.factorise m in
      let rec check_prime k q ind =
        if is_one (pow x k) then ind
        else check_prime (Base.(k * q)) q (ind + 1)
      in
      List.fold_left (fun acc (q, e) ->
        let p_val_pow_e = Base.pow q (Base.of_int e) in
        let k_init = Base.(m / p_val_pow_e) in
        let ind = check_prime k_init q 0 in
        let term = Base.pow q (Base.of_int ind) in
        Base.(acc * term)
      ) Base.one factor_list

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

module EF_Bigint = Make (Field_intf.Bigint_scalar)

module EF_Int = Make (Field_intf.Int_scalar)
