from test_support import prove_all

# The limit family carries the Override_Warn multiplicity: repeating one of
# these switches on a single command line keeps only the last occurrence and
# now warns about the silently dropped one. The two occurrences below target
# different subprograms, so the output also shows that the last one wins.
prove_all(opt=["--limit-subp=p.ads:2", "--limit-subp=p.ads:4"])
print("====== a single occurrence must not warn ================")
prove_all(opt=["--limit-subp=p.ads:2"])
print("====== the warning applies to the whole limit family ================")
prove_all(opt=["--limit-line=p.adb:4", "--limit-line=p.adb:4"])
print("====== repetition inside one project attribute warns ================")
# A project-file attribute is a source of its own, so a repetition there warns
# just like on the command line, and the last occurrence (Decrement) wins.
prove_all(project="repeat_in_attribute.gpr")
print("====== project file plus command line does not warn ================")
# Here each source carries a single occurrence, so nothing is dropped within a
# source and no warning is expected. The command line still overrides the
# project file, so only Decrement is analyzed.
prove_all(project="single_in_attribute.gpr", opt=["--limit-subp=p.ads:4"])
