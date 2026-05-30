(* tests.ml - Finite Fields Test Suite *)

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
  let a = Extensionff.gen gf in
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

let test_f2n_inverse () =
  let g = Bigint.of_int 283 in
  let a = Bigint.of_int 83 in
  let inv_a = F2n.inverse a g in
  let prod = F2n.mult a inv_a g in
  if not (Bigint.equal prod Bigint.one) then
    failwith (Printf.sprintf "test_f2n_inverse failed: expected 1, got %s" (Bigint.to_string prod))

let run_all_tests () =
  Printf.printf "Running testAdd 1...\n%!";
  test_add1 ();
  Printf.printf "Running testExp 1...\n%!";
  test_exp1 ();
  Printf.printf "Running testExp 2...\n%!";
  test_exp2 ();
  Printf.printf "Running testF2nInverse...\n%!";
  test_f2n_inverse ();
  Printf.printf "All tests completed successfully!\n%!"
