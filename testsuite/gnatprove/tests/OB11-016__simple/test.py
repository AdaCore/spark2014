from test_support import gcc, prove_all

prove_all()

# also check compilation of code with compile-time known division by zero
gcc("main.adb")
gcc("div_zero.adb")
