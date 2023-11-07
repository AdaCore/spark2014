from test_support import prove_all

print("====== expect single line ================")
prove_all(opt=["--limit-name=unique"])
print("====== expect single line ================")
prove_all(opt=["--limit-name=Unique"])
print("====== expect two lines ================")
prove_all(opt=["--limit-name=proc"])
print("====== expect two lines ================")
prove_all(opt=["--limit-name=over"])
