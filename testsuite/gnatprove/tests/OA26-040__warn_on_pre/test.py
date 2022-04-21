from test_support import clean, prove_all

print("all provers")
print("----------------")
prove_all(opt=["--proof-warnings"])
clean()

print("")
print("only CVC4")
print("----------------")
prove_all(prover=["cvc5"], opt=["--proof-warnings"])
clean()

print("")
print("only Z3")
print("----------------")
prove_all(prover=["z3"], opt=["--proof-warnings"])
clean()

print("")
print("only Alt-Ergo")
print("----------------")
prove_all(prover=["altergo"], opt=["--proof-warnings"])
clean()
