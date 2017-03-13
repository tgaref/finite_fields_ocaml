open Core.Std

module FF : sig
  type t
  type element

  val create : ?pol:(string list) -> string -> t
  val elem : t -> string list -> element
  val get_char : t -> Z.t
  val get_value : element -> Z.t list
  val get_field : element -> t

  val show : element -> string list

  val zero_elt : t -> element
  val one_elt : t -> element
    
  val add : element -> element -> element
  val mult : element -> element -> element
  val neg : element -> element
  val inv : element -> element

  val power : element -> Z.t -> element
    
end = struct
  type t = {ch : Z.t;
            deg : int;
            poly : Z.t list}
         
  type element = {value : Z.t list;
                  field : t}

  let drop_last lst elt =
    let rec drop l e =
      match l with
      |[] -> []
      |(x::xs) -> if x = elt then drop xs e
                  else l in
    let lst' = drop (List.rev lst) elt in
    List.rev lst'

  let zero = Z.of_int 0

  let one = Z.of_int 1
              
  let create ?(pol=[]) p =
    let deg = if pol =[] then 1
              else (List.length pol) - 1
    in
    let ch = Z.of_string p in
    let poly = List.map pol ~f:Z.of_string in
    if not (Base.P.irreduc poly ch) then failwith "Polynomial is not irreducible..."
    else if not (Z.probab_prime ch 10 > 0) then failwith "Characteristic must be prime..."
    else {ch; deg; poly}

  let zero_elt ff = {value = []; field = ff}
  let one_elt ff = {value = [one]; field = ff}
  let elem ff a =
    let temp = List.take (List.map a ~f:(fun i -> Z.erem (Z.of_string i) ff.ch)) ff.deg in
    {value = drop_last temp zero; field = ff}

  let get_char ff = ff.ch
  let get_deg ff = ff.deg
  let get_poly ff = ff.poly
                                   
  let get_value elt = elt.value  
  let get_field elt = elt.field

  let show elt = List.map elt.value ~f:Z.to_string

  let add_prime x y =
    let (x'::xs) = x.value in
    let (y'::ys) = y.value in
    let v = [Base.F.add x' y' x.field.ch] in
    {value = drop_last v zero; field = x.field}

  let add_ext x y =
    let v = Base.P.add x.value y.value x.field.ch in
    {value = drop_last v zero; field = x.field}
          
  let add x y =
    match x.field = y.field with
    | false -> failwith "Elements belong to different fields..."
    | true  -> match x.value, y.value with
               |v,[] -> x
               |[],v -> y
               |_,_ -> if x.field.deg = 1 then add_prime x y
                       else add_ext x y

  let mult_prime x y =
    let (x'::xs) = x.value in
    let (y'::ys) = y.value in
    let v = [Base.F.mult x' y' x.field.ch] in
    {value = drop_last v zero; field = x.field}

  let mult_ext x y =
    let pol = x.field.poly in
    let v = Base.P.mult x.value y.value x.field.ch in
    let (q,r) = Base.P.div_rem v pol x.field.ch in
    {value = drop_last r zero; field = x.field}
    
  let mult x y =
    match x.field = y.field with
    | false -> failwith "Cannot multiply elements of different fields..."
    | true  -> match x.value, y.value with
               |v,[] -> zero_elt x.field
               |[],v -> zero_elt x.field
               |_,_ -> if x.field.deg = 1 then mult_prime x y
                       else mult_ext x y

  let neg x =
    let v = List.map x.value ~f:(fun a -> Base.F.neg a x.field.ch) in
    {value = v; field = x.field}

  let inv_prime x =
    let (x'::xs) = x.value in
    let v = [Base.F.inv x' x.field.ch] in
    {value = v; field = x.field}

  let inv_ext x =
    let pol = x.field.poly in
    let (d,s,t) = Base.P.gcdext x.value pol x.field.ch in
    {value = drop_last s zero; field = x.field}
    
  let inv x =
    match x.value with
    |[] -> failwith "Zero element has no inverse..."
    |_ -> if x.field.deg = 1 then inv_prime x
          else inv_ext x

  let print_elt a =
    List.iter (show a) ~f:(fun s -> printf "%s " s);
    printf "\n"

  let power a n =
    let one_ff = one_elt a.field in
    let rec pow x b m =
      if m = zero then b
      else if m = one then mult x b
      else let (m',r) = Z.ediv_rem m (Z.of_int 2) in
           let y = mult x x in
           if r = zero then pow y b m'
           else pow y (mult x b) m' in
    pow a one_ff n
    
end
