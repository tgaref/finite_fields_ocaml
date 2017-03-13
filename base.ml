open Core.Std

module F : sig

  type element = Z.t

  val show : element -> string

  val zero_elt : element
  val one_elt : element

  val add : element -> element -> Z.t -> element
  val mult : element -> element -> Z.t -> element
  val neg : element -> Z.t -> element
  val inv : element -> Z.t -> element

  val power : element -> Z.t -> Z.t -> element
    
end = struct
  type element = Z.t

  let show elt = Z.to_string elt

  let zero_elt = Z.of_int 0

  let one_elt = Z.of_int 1
                                                    
  let add x y p = Z.erem (Z.add x y) p

  let mult x y p = Z.erem (Z.mul x y) p

  let neg x p = Z.erem (Z.neg x) p

  let inv x p = Z.invert x p

  let power a n p = Z.powm a n p
    
end

module P : sig
  type element = F.element list

  val show : element -> string list

  val zero_poly : element

  val lc : element -> F.element
  val deg : element -> int
    
  val add : element -> element -> Z.t -> element
  val mult : element -> element -> Z.t -> element
  val neg : element -> Z.t -> element
  val div_rem : element -> element -> Z.t -> element*element
  val gcdext : element -> element -> Z.t -> element*element*element
  val irreduc : element -> Z.t -> bool
    
end = struct
  type element = F.element list

  let drop_last lst elt =
    let rec drop l e =
      match l with
      |[] -> []
      |(x::xs) -> if x = elt then drop xs e
                  else l in
    let lst' = drop (List.rev lst) elt in
    List.rev lst'

  let append l n e =
    let l' = List.init n ~f:(fun i->e) in
      List.append l l'
      
  let adjust_size l1 l2 e =
    let a = List.length l1 in
    let b = List.length l2 in
    if a=b then (l1,l2)
    else
      begin
        if a>b then (l1, append l2 (a-b) e)
        else  (append l1 (b-a) e, l2)
      end

  let extend l n e =
    if List.length l >= n then l
    else append l (n-(List.length l)) e

  let rec my_zip oper l1 l2 =
    match l1,l2 with
    |l1,[] -> l1
    |[],l2 -> l2
    |(x::xs),(y::ys) -> (oper x y) :: (my_zip oper xs ys)

  let show poly = List.map poly ~f:(F.show)

  let zero_poly  = []

  let lc f =
    match f with
    |[] -> failwith "Zero polynomial..."
    |(x::xs)  -> List.last_exn f

  let deg poly = (List.length poly) - 1

  let add a b p =
    match a,b with
    |[],b -> b
    |a,[] -> a
    |(x::xs),(y::ys) -> let zero = F.zero_elt in
                        let (a',b') = adjust_size a b zero in
                        let c = List.map2_exn a' b' ~f:(fun x y -> F.add x y p) in
                        drop_last c zero

  let mult f g p =
    match f,g with
    |[],_ -> []
    |_,[] -> []
    |(x::xs),(y::ys) -> let zero = F.zero_elt in
                        let coef v u n =
                          let v' = extend (List.take v (n+1)) (n+1) zero in
                          let u' = extend (List.take u (n+1)) (n+1) zero in
                          let u'' = List.rev u' in
                          let temp = List.map2_exn v' u'' ~f:(fun a b ->
                                                     F.mult a b p) in
                          List.fold_left temp ~init: zero ~f:(fun a b ->
                                           F.add a b p) in

                        let l = List.init ((deg f) + (deg g) + 1)
                                          ~f:(fun n -> coef f g n) in
                        drop_last l zero
         
  let neg f p =
    List.map f ~f:(fun x -> F.neg x p)

  let div f g p =
    if deg f < deg g then []
    else
      begin
        let zero = F.zero_elt in
        let rec step v u l =
          if List.length v < List.length u then l
          else let temp = F.mult (List.hd_exn v) (F.inv (List.hd_exn u) p) p in
               let subtr = if temp = zero then []
                           else List.map u ~f:(fun x -> F.neg (F.mult x temp p) p) in
               let newf = if temp = zero then List.tl_exn v
                          else List.tl_exn (my_zip (fun a b -> F.add a b p) v subtr) in
               (step newf u (temp::l)) in
        let v = step (List.rev f) (List.rev g) [] in
        drop_last v zero
      end

  let div_rem f g p =
    let quo = div f g p in
    let rem = add f (neg (mult g quo p) p) p in
    (quo, rem)

  let scalar c f p =
    match f with
    |[] -> []
    |(x::xs) -> let zero = F.zero_elt in
                if c = zero then []
                else List.map f ~f:(fun a -> F.mult c a p)

  let rec gcd f g p =
    match g with
    |[] -> let (x::xs) = f in
           let one = F.one_elt in
           (f, [one], [])
    |g -> let (quo,rem) = div_rem f g p in
          let (d,s',t') = gcd g rem p in
          (d,t', add s' (neg (mult quo  t' p) p) p)

  let gcdext f g p =
    match deg f < deg g with
    |true  -> let (d,t,s) = gcd g f p in
              let c = F.inv (lc d) p in
              (scalar c d p, scalar c s p, scalar c t p)
    |false -> let (d,s,t) = gcd f g p in
              let c = F.inv (lc d) p in
              (scalar c d p, scalar c s p, scalar c t p)

  let powermod f n g p =
    let zero = Z.of_int 0 in
    let one = Z.of_int 1 in
    let one_poly = [one] in
    let rec powmod f b n =
      if n = zero then b
      else if n = one then let (_,rem) = div_rem (mult f b p) g p in rem
      else let (n',r) = Z.ediv_rem n (Z.of_int 2) in
           let (_,f') = div_rem (mult f f p) g p in
           if r = zero then powmod f' b n'
           else powmod f' (mult f b p) n'
    in
    powmod f one_poly n


  let irreduc f p =
    let zero = Z.of_int 0 in
    let one = Z.of_int 1 in
    let f = drop_last f zero in
    let d = deg f in
    if d <= 0 then false
    else if d = 1 then true
    else let one_poly = [one] in
         let bound = d/2 + 1 in
         let x = [zero;one] in
         let x' = neg x p in
         let rec step n h =
           if n >= bound then true
           else let (g,s,t) = gcdext f (add h x p) p in
                if g = one_poly then step (n+1) (powermod h p f p)
                else false
         in
         step 1 (powermod x p f p)
end    
