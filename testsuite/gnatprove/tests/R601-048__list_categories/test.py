from test_support import gnatprove, default_refiners_no_sort

gnatprove(opt=["--list-categories"], refiners=default_refiners_no_sort())
