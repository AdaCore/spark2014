from test_support import prove_all, gnatprove

print("====== expect single line ================")
prove_all(opt=["--limit-name=unique"])
print("====== expect single line ================")
prove_all(opt=["--limit-name=Unique"])
print("====== expect two lines ================")
prove_all(opt=["--limit-name=proc"])
print("====== expect two lines ================")
prove_all(opt=["--limit-name=over"])
print("====== expect no output, plus error ================")
gnatprove(opt=["-P", "test.gpr", "--limit-name=clover"], exit_status=1)
