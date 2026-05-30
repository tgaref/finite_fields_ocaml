(* arith.ml - Shared Math Utility Module *)

open Core

module Make (Base : Field_intf.BASE_FIELD) = struct
  let factorise n =
    let n = ref n in
    let factors = ref [] in
    let two = Base.of_int 2 in
    let count2 = ref 0 in
    while let open Base in Base.equal (!n % two) Base.zero && Base.compare !n Base.zero > 0 do
      count2 := !count2 + 1;
      let open Base in
      n := !n / two
    done;
    if !count2 > 0 then factors := (two, !count2) :: !factors;
    let d = ref (Base.of_int 3) in
    while let open Base in Base.compare (!d * !d) !n <= 0 do
      let count = ref 0 in
      while let open Base in Base.equal (!n % !d) Base.zero do
        count := !count + 1;
        let open Base in
        n := !n / !d
      done;
      if !count > 0 then factors := (!d, !count) :: !factors;
      d := let open Base in !d + two
    done;
    if let open Base in Base.compare !n Base.one > 0 then factors := (!n, 1) :: !factors;
    List.rev !factors
end

include Make (Field_intf.Bigint_scalar)
