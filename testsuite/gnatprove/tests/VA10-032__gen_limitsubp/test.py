from test_support import prove_all

prove_all(opt=["--limit-subp=main.adb:9:gen_pack.ads:5"])
print("=================")
prove_all(opt=["--limit-subp=main.adb:10:gen_pack.ads:5"])
print("=================")
prove_all(opt=["--limit-subp=gen_pack.ads:5", "-U"])
