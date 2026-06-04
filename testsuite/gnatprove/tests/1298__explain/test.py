from test_support import gnatprove

gnatprove(opt=["--explain", "E0010"], info=False, refiners=[])
