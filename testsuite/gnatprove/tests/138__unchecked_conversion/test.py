from subprocess import call
from test_support import gprbuild, prove_all

gprbuild(["-q", "-gnata", "modular.adb"])
call(["./modular"])
gprbuild(["-q", "-gnata", "signed.adb"])
call(["./signed"])
prove_all()
