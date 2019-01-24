from test_support import *

# First we generate an up-to-date ali file for foo
prove_all(opt=["-u", "foo.adb"])

# Then we transform it into something that looks like 15.0.2
with open(os.path.join("gnatprove", "phase1", "foo.ali"), "r") as src:
    lines = src.read().splitlines()
with open(os.path.join("gnatprove", "phase1", "foo.ali"), "w") as dst:
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

# Then we attempt to prove everything (i.e. bar) but using the broken
# foo.ali
prove_all()
