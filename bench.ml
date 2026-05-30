(* bench.ml - Finite Fields Benchmark Suite *)

module Primeff = Primeff.PF_Bigint
module Extensionff = Extensionff.EF_Bigint
module F2n = F2n.F2N_Bigint

let time_it label n f =
  let t0 = Sys.time () in
  for _ = 1 to n do
    ignore (f ())
  done;
  let t1 = Sys.time () in
  Printf.printf "%s: %.4f seconds\n%!" label (t1 -. t0);
  t1 -. t0

let () =
  Printf.printf "Starting OCaml Benchmarks (1,000,000 iterations)...\n%!";
  
  (* 1. Prime Field *)
  let p = Bigint.of_string "1000000007" in
  let gf_p = Primeff.create p in
  let a_p = Primeff.element gf_p (Bigint.of_string "123456789") in
  let b_p = Primeff.element gf_p (Bigint.of_string "987654321") in
  
  let _ = time_it "Prime Field Addition" 1000000 (fun () -> Primeff.add a_p b_p) in
  let _ = time_it "Prime Field Multiplication" 1000000 (fun () -> Primeff.mul a_p b_p) in

  (* 2. Extension Field *)
  let poly = Array.concat [ [|Bigint.one; Bigint.of_int 2|]; Array.make 13 Bigint.zero; [|Bigint.one|] ] in
  let gf_ext = Extensionff.create (Bigint.of_int 11) poly "a" in
  let a_ext = Extensionff.element gf_ext (Array.map Bigint.of_int [|1;4;0;7;1;2;3;4;5;6;7;8;9;10|]) in
  let b_ext = Extensionff.element gf_ext (Array.map Bigint.of_int [|4;6;2;5;1;8;3;4;10;10;3;2;10;1|]) in

  let _ = time_it "Extension Field Addition" 1000000 (fun () -> Extensionff.add a_ext b_ext) in
  let _ = time_it "Extension Field Multiplication" 1000000 (fun () -> Extensionff.mul a_ext b_ext) in

  (* 3. F2n Field *)
  let g = Bigint.of_int 283 in
  let a_f2n = Bigint.of_int 83 in
  let b_f2n = Bigint.of_int 193 in

  let _ = time_it "F2n Addition" 1000000 (fun () -> F2n.add a_f2n b_f2n) in
  let _ = time_it "F2n Multiplication" 1000000 (fun () -> F2n.mult a_f2n b_f2n g) in
  ()
