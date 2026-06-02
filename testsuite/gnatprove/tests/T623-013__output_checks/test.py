from test_support import (
    gnatprove,
    prove_all,
    default_refiners_no_sort,
)

print("default command-line output")
print("---------------------------")
gnatprove(
    opt=["-q", "-P", "test.gpr"],
    refiners=default_refiners_no_sort(),
)
print("")

print("brief output")
print("------------")
prove_all(opt=["--output=brief"], sort_output=False)
print("")

print("pretty output")
print("-------------")
prove_all(opt=["--output=pretty"], sort_output=False)
print("")

print("one-line output")
print("---------------")
prove_all(opt=["--output=oneline"], sort_output=False)
print("")

print("incorrect output value")
print("----------------------")
prove_all(opt=["--output=whatever"], sort_output=False)
