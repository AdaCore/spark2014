from test_support import *
from gnatpython.ex import Run

def which(program):
    import os
    def is_exe(fpath):
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    if os.name != 'posix':
        program = program + ".exe"
    fpath, fname = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            path = path.strip('"')
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                return exe_file

    return None

binpath = os.path.dirname(which("gnatprove"))
share_path = os.path.join(os.path.dirname(binpath),
                          "share")
driver_path = os.path.join(os.path.join(os.path.join(share_path, "why3"),
                                        "drivers"),
                           "coq.drv")

# create why3 configuration file
whyconf = open('test.whyconf', 'w')

whyconf.write('[main]' + os.linesep)
whyconf.write('magic = 14')
whyconf.write(os.linesep)
whyconf.write('[prover]' + os.linesep)
whyconf.write('command = "echo %f"' + os.linesep)
whyconf.write('driver = "' + driver_path + '"' + os.linesep)
whyconf.write('in_place = false' + os.linesep)
whyconf.write('interactive = true' + os.linesep)
whyconf.write('name = "Qoc"' + os.linesep)
whyconf.write('shortcut = "qoc"' + os.linesep)
whyconf.write('version = "X"' + os.linesep)
whyconf.write('configure_build = "cp %f %f.configured"' + os.linesep)
whyconf.write('build_commands = "cp %f %f.built"' + os.linesep)

whyconf.close()

Run(["gnatprove", "-Ptest.gpr",
     "--limit-line=test_if.ads:5:37:VC_OVERFLOW_CHECK",
     "--prover=Qoc",
     "--why3-conf=test.whyconf"])

ls("gnatprove/user/Qoc")
