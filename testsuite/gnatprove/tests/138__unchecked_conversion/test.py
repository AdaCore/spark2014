from subprocess import call
from test_support import prove_all

call(["gnatmake", "-q", "-gnata", "modular.adb"])
call(["./modular"])
call(["gnatmake", "-q", "-gnata", "signed.adb"])
call(["./signed"])
prove_all()
