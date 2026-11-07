from test_support import do_flow


print("Client only")
do_flow(opt=["-u", "client.adb"])
print("Declaring unit and client")
do_flow(opt=["-U", "-f"])
