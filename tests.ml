(* tests.ml - Finite Fields Test Suite *)

module EF_Int = Extensionff.EF_Int
module F2N_Int = F2n.F2N_Int
module Extensionff = Extensionff.EF_Bigint
module F2n = F2n.F2N_Bigint

let assert_equal_elem a b msg =
  if not (Extensionff.equal a b) then
    failwith (Printf.sprintf "Assertion failed: %s\nExpected: %s\nGot: %s" msg (Extensionff.show b) (Extensionff.show a))

let test_add1 () =
  let poly = Array.concat [ [|Bigint.one; Bigint.one; Bigint.one; Bigint.one|]; Array.make 16 Bigint.zero; [|Bigint.one|] ] in
  let gf = Extensionff.create (Bigint.of_int 2) poly "a" in
  let b = Extensionff.element gf (Array.map Bigint.of_int [|1;0;0;1;0;0;1;0;1;1;0;1;0;0|]) in
  let c = Extensionff.element gf (Array.map Bigint.of_int [|1;1;1;0;0;0;1;0;0;1;1;0;0;0;0;1;0;0;1;0|]) in
  let d = Extensionff.element gf (Array.map Bigint.of_int [|0;1;1;1;0;0;0;0;1;0;1;1;0;0;0;1;0;0;1|]) in
  assert_equal_elem (Extensionff.add b c) d "test_add1"

let test_exp1 () =
  let poly = Array.concat [ [|Bigint.one; Bigint.of_int 2|]; Array.make 13 Bigint.zero; [|Bigint.one|] ] in
  let gf = Extensionff.create (Bigint.of_int 11) poly "a" in
  let one = Extensionff.one gf in
  let a = Extensionff.get_generator gf in
  let b = Extensionff.element gf (Array.map Bigint.of_int [|1;4;0;7|]) in
  let n = Bigint.of_string "1234567890987654321" in
  let c =
    let term14 = Extensionff.scalar_mul (Bigint.of_int 10) (Extensionff.pow a (Bigint.of_int 14)) in
    let term13 = Extensionff.pow a (Bigint.of_int 13) in
    let term12 = Extensionff.scalar_mul (Bigint.of_int 10) (Extensionff.pow a (Bigint.of_int 12)) in
    let term11 = Extensionff.scalar_mul (Bigint.of_int 2) (Extensionff.pow a (Bigint.of_int 11)) in
    let term10 = Extensionff.scalar_mul (Bigint.of_int 3) (Extensionff.pow a (Bigint.of_int 10)) in
    let term9 = Extensionff.scalar_mul (Bigint.of_int 10) (Extensionff.pow a (Bigint.of_int 9)) in
    let term8 = Extensionff.scalar_mul (Bigint.of_int 10) (Extensionff.pow a (Bigint.of_int 8)) in
    let term7 = Extensionff.scalar_mul (Bigint.of_int 4) (Extensionff.pow a (Bigint.of_int 7)) in
    let term6 = Extensionff.scalar_mul (Bigint.of_int 3) (Extensionff.pow a (Bigint.of_int 6)) in
    let term5 = Extensionff.scalar_mul (Bigint.of_int 8) (Extensionff.pow a (Bigint.of_int 5)) in
    let term4 = Extensionff.pow a (Bigint.of_int 4) in
    let term3 = Extensionff.scalar_mul (Bigint.of_int 5) (Extensionff.pow a (Bigint.of_int 3)) in
    let term2 = Extensionff.scalar_mul (Bigint.of_int 2) (Extensionff.pow a (Bigint.of_int 2)) in
    let term1 = Extensionff.scalar_mul (Bigint.of_int 6) a in
    let term0 = Extensionff.scalar_mul (Bigint.of_int 4) one in
    List.fold_left Extensionff.add term14 [term13; term12; term11; term10; term9; term8; term7; term6; term5; term4; term3; term2; term1; term0]
  in
  assert_equal_elem (Extensionff.pow b n) c "test_exp1"

let test_exp2 () =
  let poly = Array.concat [ [|Bigint.one; Bigint.of_int 2|]; Array.make 13 Bigint.zero; [|Bigint.one|] ] in
  let gf = Extensionff.create (Bigint.of_int 11) poly "a" in
  let b = Extensionff.element gf (Array.map Bigint.of_int [|1;4;0;7|]) in
  let n = Bigint.of_string "1234567890987654321" in
  let c = Extensionff.element gf (Array.map Bigint.of_int [|4;6;2;5;1;8;3;4;10;10;3;2;10;1;10|]) in
  assert_equal_elem (Extensionff.pow b n) c "test_exp2"

let test_gf3_10 () =
  let p = Bigint.of_int 3 in
  let poly = Array.map Bigint.of_int [|2; 0; 2; 0; 1; 2; 0; 0; 0; 0; 1|] in
  let gf = Extensionff.create p poly "a" in
  let gen = Extensionff.get_generator gf in
  let ord = Extensionff.order gen in
  if not (Bigint.equal ord (Bigint.of_int 59048)) then
    failwith (Printf.sprintf "test_gf3_10 failed: expected generator order 59048, got %s" (Bigint.to_string ord))


let test_f2n_inverse () =
  let poly = Array.map Bigint.of_int [|1; 1; 0; 1; 1; 0; 0; 0; 1|] in
  let gf = F2n.create (Bigint.of_int 2) poly "a" in
  let a_val = Array.map Bigint.of_int [|1; 1; 0; 0; 1; 0; 1|] in
  let a = F2n.element gf a_val in
  let inv_a = F2n.inv a in
  let prod = F2n.mul a inv_a in
  if not (F2n.is_one prod) then
    failwith "test_f2n_inverse failed: expected 1"

let test_f2n_rand_and_generator () =
  let poly = Array.map Bigint.of_int [|1; 1; 0; 1; 1; 0; 0; 0; 1|] in
  let gf = F2n.create (Bigint.of_int 2) poly "a" in
  (* Test random elements *)
  for _ = 1 to 20 do
    let r = F2n.get_rand_elt gf in
    if Bigint.compare r.value (Bigint.of_int 256) >= 0 || Bigint.compare r.value Bigint.zero < 0 then
      failwith (Printf.sprintf "test_f2n_rand_and_generator failed: random element %s out of range" (Bigint.to_string r.value))
  done;
  (* Test generator *)
  let gen = F2n.get_generator gf in
  let p255 = F2n.pow gen (Bigint.of_int 255) in
  if not (F2n.is_one p255) then
    failwith "test_f2n_rand_and_generator failed: gen^255 expected 1";
  List.iter (fun q ->
    let exp = Bigint.of_int (255 / q) in
    let pq = F2n.pow gen exp in
    if F2n.is_one pq then
      failwith (Printf.sprintf "test_f2n_rand_and_generator failed: gen^(255/%d) expected not 1, got 1" q)
  ) [3; 5; 17]

let test_gf3_100_overflow () =
  let p = 3 in
  let rec find_poly () =
    let rand_state = Random.State.make_self_init () in
    let poly = Array.init 42 (fun i ->
      if i = 41 then 1
      else Random.State.int rand_state 3
    ) in
    (* We can check irreducibility using Aux_Int *)
    let module Aux_Int = Aux.Make(Field_intf.Int_scalar) in
    let poly' = Aux_Int.drop_last poly in
    if Aux_Int.irreduc poly' p then poly
    else find_poly ()
  in
  let poly = find_poly () in
  try
    let _ = EF_Int.create p poly "a" in
    failwith "test_gf3_100_overflow failed: expected overflow exception, but succeeded"
  with
  | Failure _ ->
      ()
  | e ->
      failwith (Printf.sprintf "test_gf3_100_overflow failed: caught unexpected exception: %s" (Printexc.to_string e))

let test_f2n_overflow () =
  let poly = Array.init 65 (fun i -> if i = 64 then 1 else 0) in
  try
    let _ = F2N_Int.create 2 poly "a" in
    failwith "test_f2n_overflow failed: expected overflow exception, but succeeded"
  with
  | Failure _ ->
      ()
  | e ->
      failwith (Printf.sprintf "test_f2n_overflow failed: caught unexpected exception: %s" (Printexc.to_string e))

let run_all_tests () =
  Printf.printf "Running testAdd 1...\n%!";
  test_add1 ();
  Printf.printf "Running testExp 1...\n%!";
  test_exp1 ();
  Printf.printf "Running testExp 2...\n%!";
  test_exp2 ();
  Printf.printf "Running testGF3_10...\n%!";
  test_gf3_10 ();
  Printf.printf "Running testGF3_100_overflow...\n%!";
  test_gf3_100_overflow ();
  Printf.printf "Running testF2nInverse...\n%!";
  test_f2n_inverse ();
  Printf.printf "Running testF2nRandAndGenerator...\n%!";
  test_f2n_rand_and_generator ();
  Printf.printf "Running testF2nOverflow...\n%!";
  test_f2n_overflow ();
  Printf.printf "All tests completed successfully!\n%!"


