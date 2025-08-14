from test_support import prove_all

print("===== --config without existing file should fail =======")
prove_all(opt=["--config=conf.cgpr"])
print("===== --autoconf should work regardless of existence of file =======")
prove_all(opt=["--autoconf=conf.cgpr"])
print("===== --autoconf second invocation =======")
prove_all(opt=["--autoconf=conf.cgpr"])
print("===== --config should work now =======")
prove_all(opt=["--config=conf.cgpr"])
