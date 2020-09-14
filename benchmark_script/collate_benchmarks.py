#!/usr/bin/env python

import os
import shutil

bm = {}

smt2_driver_prefix = ";; produced by "

for path, dirs, files in os.walk("data"):
    for f in files:
        if f.endswith(".smt2") or f.endswith(".why"):
            # Strip extension and trailing numbers added by why3
            tmp = f.rsplit(".", 1)[0]
            vc_name = tmp.rstrip("0123456789")
            vc_index = tmp[len(vc_name):]
            if vc_index == "":
                vc_index = 1
            else:
                vc_index = int(vc_index)

            test_name = path.split("/")[2]
            name = test_name + "__" + vc_name
            name = name.replace(" ", "_")

            if f.endswith(".smt2"):
                prover = None
                with open(os.path.join(path, f)) as fd:
                    for raw_line in fd:
                        if raw_line.startswith(smt2_driver_prefix):
                            prover = raw_line[len(smt2_driver_prefix):]
                            prover = prover.split()[0].rsplit(".", 1)[0]
                            break
                assert prover is not None
            else:
                prover = "altergo"

            if name not in bm:
                bm[name] = {prover: [os.path.join(path, f)]}
            elif prover not in bm[name]:
                bm[name][prover] = [os.path.join(path, f)]
            else:
                bm[name][prover].append(os.path.join(path, f))

PROVERS = set()
for name in bm:
    PROVERS |= set(bm[name])
    # p = False
    # for x in bm[name]:
    #     p |= len(bm[name][x]) > 1
    # if p:
    #     print bm[name]
PROVERS = sorted(PROVERS)

# ignored = []
# for test in sorted(bm):
#     if len(bm[test]) == 1:
#         print "Ignoring test %s without comparison results..." % test
#         ignored.append(test)
#
# for i in ignored:
#     del bm[i]

EXT = {
    "altergo": "why",
    "cvc4_16": "smt2",
    "z3_gnatprove": "smt2",
    "z3_gnatprove_ce":  "smt2",
}

for p in PROVERS:
    os.makedirs(os.path.join("bench", p))

for test in bm:
    for p in PROVERS:
        if p in bm[test]:
            for id, the_test in enumerate(sorted(bm[test][p])):
                dst = os.path.join("bench",
                                   p,
                                   test + ("__%02u" % id) + "." + EXT[p])
                assert (not os.path.exists(dst))
                shutil.copyfile(the_test, dst)
