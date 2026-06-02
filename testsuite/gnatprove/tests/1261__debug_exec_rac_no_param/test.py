from test_support import prove_all, default_refiners_no_sort

prove_all(opt=["--debug-exec-rac"], refiners=default_refiners_no_sort())
