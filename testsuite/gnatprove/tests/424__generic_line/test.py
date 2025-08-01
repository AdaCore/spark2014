from test_support import prove_all

prove_all()
print("======= expect only instance at line 4 =========")
prove_all(opt=["--limit-line=main.adb:4:gen.adb:5"])
print("======= expect only instance at line 6 =========")
prove_all(opt=["--limit-line=main.adb:6:gen.adb:5"])
print("======= expect only instance at line 11 =========")
prove_all(opt=["--limit-line=main.adb:11:gen.adb:5:12:VC_RANGE_CHECK"])
print("======= expect only instance at line 13, instance line 7 =========")
prove_all(opt=["--limit-line=main.adb:13:gen2.ads:7:gen.adb:5"])
print("======= expect only instance at line 13, instance line 7 =========")
prove_all(opt=["--limit-region=main.adb:13:gen2.ads:7:gen.adb:5:6"])
print("======= expect only instance at line 4 =========")
prove_all(opt=["--limit-region=main.adb:4:gen.adb:5:6"])
