from test_support import *
from gnatpython.ex import Run
from gnatpython import fileutils

installdir = os.path.dirname(os.path.dirname(fileutils.which('gnatprove')))
driverdir = os.path.join(installdir, 'share', 'why3', 'drivers')
driverfile = os.path.join(driverdir, 'coq.drv')

# create why3 configuration file
whyconf = open('test.whyconf', 'w')

whyconf.write('[main]' + os.linesep)
whyconf.write('magic = 14')
whyconf.write(os.linesep)
whyconf.write('[prover]' + os.linesep)
whyconf.write('command = "echo %f"' + os.linesep)
whyconf.write('driver = "' + driverfile + '"' + os.linesep)
whyconf.write('in_place = false' + os.linesep)
whyconf.write('interactive = true' + os.linesep)
whyconf.write('name = "Qoc"' + os.linesep)
whyconf.write('shortcut = "qoc"' + os.linesep)
whyconf.write('version = "X"' + os.linesep)
whyconf.write('configure_build = "cp %f %f.configured"' + os.linesep)
whyconf.write('build_commands = "cp %f %f.built"' + os.linesep)

whyconf.close()

prove_all(opt=[
     "--limit-line=test_if.ads:5:37:VC_OVERFLOW_CHECK",
     "--prover=Qoc",
     "--why3-conf=test.whyconf"])

ls("gnatprove/user/Qoc")
