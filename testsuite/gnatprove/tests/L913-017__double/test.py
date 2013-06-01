from test_support import altergo

altergo("double_forall_k.smt")
altergo("reduced_2.smt")
altergo("reduced.smt", timeout=20)
altergo("test_div_a-1.smt")
