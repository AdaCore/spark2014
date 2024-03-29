from test_support import gcc, prove_all
import os.path

gcc(
    os.path.join("adainclude", "system.ads"),
    opt=["-c", "-gnatg", "-o" + os.path.join("adalib", "system.o")],
)

prove_all(opt=["--RTS=."])
