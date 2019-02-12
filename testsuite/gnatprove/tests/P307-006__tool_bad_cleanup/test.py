from test_support import *
import os

# First we generate an up-to-date ali file for foo
prove_all(opt=["-u", "foo.adb"])

# Then we transform it into something that looks like 15.0.2, but preserving
# the filesystem timestamp of the generated ALI file.
ali = os.path.join("gnatprove", "phase1", "foo.ali")
statinfo = os.stat(ali)

with open(ali, "r") as src:
    lines = src.read().splitlines()
with open(ali, "w") as dst:
    for l in lines:
        if l.startswith("QQ SPARKVERSION"):
            break
        dst.write(l + "\n")
    dst.write("GG S foo__p\n")
    dst.write("GG VP\n")
    dst.write("GG VI\n")
    dst.write("GG VO foo__g\n")
    dst.write("GG CP\n")
    dst.write("GG CD\n")
    dst.write("GG CC\n")
    dst.write("GG LV\n")

# ??? with python3 we could use nanosecond-resolution timestamps;
# with python2 we can only use second-resulution, but this is fine, because
# the timestamp are truncated "towards the past", so the file will appear
# older than it was.
os.utime(ali, (statinfo.st_atime, statinfo.st_mtime))

# Then we attempt to prove everything (i.e. bar) but using the broken
# foo.ali
prove_all()
