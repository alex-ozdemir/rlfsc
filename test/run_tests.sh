#!/usr/bin/env zsh

set -e

mypath=$0:A:h
tests=(
  ann_lambda.plf
  bad-char.plf
  bool.plf
  # This tests that ifequal on rationals is rational equality, not pointer.
  # Unclear that behavior is desireable.
  #eq_mpz.plf
  issue20.plf
  issue8-mpexp.plf
  formal_type_args.plf
  mp_prefix.plf
  mp_smaller_test.plf
  mpz_to_mpq.plf
  mpz_to_mpq_checks.plf
  num.plf
  redecl.plf
  redefn.plf
  reopaque.plf
  # Big test
  #sage-app2-bench_201.plf
  sat.plf
  semicolon_after_id.plf
  skolem1.plf
  skolem2.plf
  smt.plf
  th_arrays.plf
  th_base.plf
  th_bv.plf
  th_bv_bitblast.plf
  th_int.plf
  # This tests LFSC's broken behavior on unapplied lambdas
  #th_quant.plf
  unused_pi_param_rational_in_body.plf
  use-bool.plf
  use-use-bool.plf
  whr-match.plf
  sugar_provided.plf
  sugar_assuming.plf
  sugar_forall.plf
  sugar_define_const.plf
  sugar_declare_rule.plf
  sugar_declare_type.plf
  sugar_arrow.plf
  sugar_lam.plf
  sugar_let.plf
  sugar_skolem.plf
  expr_head.plf
  )

cargo build
for t in $tests
do
    echo Testing: $t
    $mypath/run_test.py $mypath/../target/debug/rlfsc $mypath/tests/$t
done
