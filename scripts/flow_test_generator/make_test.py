#!/usr/bin/env python

# A random code-generator to produce SPARK code. Useful for testing flow
# analysis, in particular the generated globals.

from copy import copy
from random import seed, randint, choice, shuffle

# All chance tunables are expressed in percent.

NUM_PACKAGES = 25
NUM_TOPLEVEL_PACKAGES = 3
EXTRA_DEP_CHANCE = 45
MULTIPLIER = 10
EXTRA_S_VAR_CHANCE = 45
EXTRA_B_VAR_CHANCE = 55
EXTRA_VAR_USE_CHANCE = 70
IN_PARAMS = [0, 1, 1, 2, 2, 3, 4, 5]
OUT_PARAMS = [0, 0, 1, 1, 2, 2, 3, 4, 5]
MAX_SUBPROGRAM_CALLS = 25

indent_depth = [0]


def pl(fd, text=""):
    s = " " * (indent_depth[0] * 3)
    s += text
    fd.write(s.rstrip())
    fd.write("\n")


def indent():
    indent_depth[0] += 1


def outdent():
    indent_depth[0] -= 1

global_var_id = [0]


def mk_global_var():
    global_var_id[0] += 1
    return "G_%03u" % global_var_id[0]


def choices(iterable, count):
    tmp = copy(list(iterable))
    rv = []
    for i in xrange(min(count, len(tmp))):
        x = randint(0, len(tmp) - 1)
        rv.append(tmp[x])
        del tmp[x]
    return rv


def guaranteed_choices(iterable, count):
    rv = choices(iterable, count)
    while len(rv) < count:
        rv.append(choice(["True", "False"]))
    shuffle(rv)
    return rv


def multiple_choices(iterable, count):
    assert len(iterable) > 0
    rv = []
    while len(rv) < count:
        rv += choices(iterable, count - len(rv))
    assert len(rv) == count
    return rv

pack = []


def lookup_subprogram(name):
    for p in pack:
        for s in p["sub"]:
            if s["name"] == name:
                return s
    assert False


def get_params(s):
    p_in = set(s["p_inputs"])
    p_out = set(s["p_outputs"])
    p_inout = p_in & p_out
    p_in = p_in - p_inout
    p_out = p_out - p_inout
    return p_in, p_inout, p_out


def emit_decl(s):
    d = s["kind"] + " " + s["name"]
    p_in, p_inout, p_out = get_params(s)

    if len(p_in) + len(p_out) + len(p_inout) > 0:
        tmp = []
        if len(p_in):
            tmp.append(", ".join(sorted(p_in)) + ": Boolean")
        if len(p_inout):
            tmp.append(", ".join(sorted(p_inout)) + ": in out Boolean")
        if len(p_out):
            tmp.append(", ".join(sorted(p_out)) + ": out Boolean")
        d += " (%s)" % "; ".join(tmp)
    if s["kind"] == "function":
        d += " return Boolean"
    return d


def emit_body(fd, s):
    list_stmt = []

    p_in, p_inout, p_out = get_params(s)
    tmp_vars = []

    req_ins = list(set(s["g_inputs"]) | p_in | p_inout)
    req_outs = list(set(s["g_outputs"]) | p_inout | p_out)

    for csn in s["calls"]:
        cs = lookup_subprogram(csn)
        if cs["kind"] == "function":
            cs_in, cs_inout, cs_out = get_params(cs)
            assert len(cs_inout) == 0 and len(cs_out) == 0
            tmp = cs["name"]
            if len(cs_in):
                args = guaranteed_choices(req_ins, len(cs_in))
                tmp += " (" + ", ".join(args) + ")"
            req_ins.append(tmp)
    shuffle(req_ins)

    for csn in s["calls"]:
        cs = lookup_subprogram(csn)
        if cs["kind"] == "function":
            continue

        cs_in, cs_inout, cs_out = get_params(cs)

        args_in = guaranteed_choices(req_ins, len(cs_in))

        possible_outputs = p_inout | p_out | set(s["g_outputs"])
        if len(possible_outputs) < len(cs_inout) + len(cs_out):
            for i in xrange((len(cs_inout) + len(cs_out)) -
                            len(possible_outputs)):
                tmp = "Tmp_%u" % (len(tmp_vars) + 1)
                tmp_vars.append(tmp)
                possible_outputs.add(tmp)

        args_inout = choices(possible_outputs, len(cs_inout))
        possible_outputs -= set(args_inout)

        args_out = choices(possible_outputs, len(cs_out))

        req_outs = list(set(req_outs) - (set(args_inout) | set(args_out)))

        assert len(cs_inout) == len(args_inout)
        assert len(cs_out) == len(args_out)

        args = args_in + args_inout + args_out

        tmp = cs["name"]
        if len(args):
            tmp += " (" + ", ".join(args) + ")"
        tmp += ";"
        list_stmt.append(tmp)

    shuffle(req_outs)
    for o in req_outs:
        my_ins = set()
        while len(req_ins):
            i = choice(req_ins)
            my_ins.add(i)
            if i in req_ins:
                req_ins.remove(i)
            if randint(1, 100) > 60:
                break
        if o == req_outs[-1]:
            my_ins |= set(req_ins)
        if len(my_ins) == 0:
            my_ins.add(choice(["True", "False"]))
        list_stmt.append("%s := %s;" % (o,
                                        " xor ".join(sorted(my_ins))))

    if s["kind"] == "function":
        list_stmt.append("return %s;" % (" xor ".join(sorted(req_ins))))

    shuffle(list_stmt)

    pl(fd, emit_decl(s))
    pl(fd, "is")
    indent()
    for tmp in tmp_vars:
        pl(fd, "%s : Boolean := %s;" % (tmp, choice(["True", "False"])))
    outdent()
    pl(fd, "begin")
    indent()
    if len(list_stmt):
        for stmt in list_stmt:
            pl(fd, stmt)
    else:
        pl(fd, "null;")
    outdent()
    pl(fd, "end %s;" % s["name"])


def emit_pkg(pkg_id):
    pkg = pack[pkg_id]

    with open("%s.ads" % pkg["name"].lower(), "w") as fd:
        for i in pkg["s_with"]:
            pl(fd, "with %s; use %s;" % (pack[i]["name"],
                                         pack[i]["name"]))
        if len(pkg["s_with"]) > 0:
            pl(fd)
        pl(fd, "package %s" % pkg["name"])
        if len(pkg["b_var"]):
            pl(fd, "with Abstract_State => State,")
            pl(fd, "     Initializes    => State")
        pl(fd, "is")
        indent()
        for v in pkg["s_var"]:
            pl(fd, "%s : Boolean;" % v)
        for s in pkg["sub"]:
            pl(fd)
            pl(fd, emit_decl(s) + ";")
        outdent()
        pl(fd, "end %s;" % pkg["name"])

    with open("%s.adb" % pkg["name"].lower(), "w") as fd:
        for i in pkg["b_with"]:
            pl(fd, "with %s; use %s;" % (pack[i]["name"],
                                         pack[i]["name"]))
        if len(pkg["b_with"]) > 0:
            pl(fd)
        pl(fd, "package body %s" % pkg["name"])
        if len(pkg["b_var"]) > 1:
            for i, v in enumerate(pkg["b_var"]):
                if i == 0:
                    tmp = "with Refined_State => (State => (%s" % v
                else:
                    tmp = "                                 %s" % v
                if i == len(pkg["b_var"]) - 1:
                    tmp += "))"
                else:
                    tmp += ","
                pl(fd, tmp)
        elif len(pkg["b_var"]) == 1:
            pl(fd, "with Refined_State => (State => %s)" % pkg["b_var"][0])
        pl(fd, "is")
        indent()
        pl(fd, """pragma Warnings (Off, "unused assignment to *");""")
        pl(fd)
        init_in_spec = []
        init_in_elab = []
        for i, v in enumerate(pkg["b_var"]):
            if randint(1, 100) > 50:
                pl(fd, "%s : Boolean := %s;" %
                   (v,
                    choice(["True", "False"] + init_in_spec)))
                init_in_spec.append(v)
            else:
                pl(fd, "%s : Boolean;" % v)
                init_in_elab.append(v)
        for s in pkg["sub"]:
            pl(fd)
            emit_body(fd, s)
        outdent()
        if len(init_in_elab):
            pl(fd)
            pl(fd, "begin")
            indent()
            for v in init_in_elab:
                pl(fd, "%s := %s;" %
                   (v,
                    choice(["True", "False"] + init_in_spec)))
            outdent()
        pl(fd, "end %s;" % pkg["name"])


def main():
    seed(0)

    # Make package structure
    for pkg_id in xrange(NUM_PACKAGES):
        pkg_name = "Package_%03u" % (pkg_id + 1)
        p = {
            "name": pkg_name,
            "s_with": [],
            "b_with": [],
            "s_var": [],
            "b_var": [],
            "sub": [],
        }

        # Add dependency on some parent
        possibilities = set(range(pkg_id))
        if pkg_id >= NUM_TOPLEVEL_PACKAGES:
            while len(possibilities) > 0:
                the_with = choice(["s_with", "b_with"])
                i = choice(list(possibilities))
                possibilities.remove(i)
                pack[i][the_with].append(pkg_id)
                if randint(1, 100) > EXTRA_DEP_CHANCE:
                    break

        # Add globals
        while True:
            for _ in xrange(MULTIPLIER):
                p["s_var"].append(mk_global_var())
            if randint(1, 100) > EXTRA_S_VAR_CHANCE:
                break
        while True:
            for _ in xrange(MULTIPLIER):
                p["b_var"].append(mk_global_var())
            if randint(1, 100) > EXTRA_B_VAR_CHANCE:
                break

        pack.append(p)

    print "Total global variables: %u" % global_var_id[0]

    # Basic procedure declarations...
    for pkg_id, p in enumerate(pack):
        req_vars = p["s_var"] + p["b_var"]
        min_subp = max(3, (len(req_vars) / (MULTIPLIER * 4)))
        num_subp = randint(min_subp, min_subp * 3)

        for s_id in xrange(num_subp):
            k = choice(["function", "procedure"])
            s = {"kind": k,
                 "name": "P_%u_%s_%u" % (pkg_id + 1,
                                         k[0].upper(),
                                         s_id + 1),
                 "g_inputs": [],
                 "g_outputs": [],
                 "p_inputs": [],
                 "p_outputs": [],
                 "calls": []}

            p_in = []
            p_out = []
            for i in xrange(choice(IN_PARAMS)):
                p_in.append(i)
            offs = randint((len(s["p_inputs"]) * 2) // 3, len(s["p_inputs"]))
            offs = 10
            for i in xrange(choice(OUT_PARAMS)
                            if s["kind"] == "procedure"
                            else 0):
                p_out.append(offs + i)
            s["p_inputs"] = [chr(65 + x) for x in p_in]
            s["p_outputs"] = [chr(65 + x) for x in p_out]

            p["sub"].append(s)

    # Now we need to add add variables + subprograms called
    for pkg_id, p in enumerate(pack):
        req_vars = p["s_var"] + p["b_var"]
        vis_pkg = p["s_with"] + p["b_with"]
        vis_vars = reduce(lambda a, b: a + b,
                          (pack[x]["s_var"] for x in vis_pkg),
                          [])
        vis_subp = reduce(lambda a, b: a + b,
                          (pack[x]["sub"] for x in vis_pkg),
                          [])

        for s_id, s in enumerate(p["sub"]):
            # Call some subprograms
            ok_subp = [x
                       for x in vis_subp
                       if x["kind"] == "function" or s["kind"] == "procedure"]
            for _ in xrange(randint(0, min(MAX_SUBPROGRAM_CALLS,
                                           len(ok_subp)))):
                tmp = randint(0, len(ok_subp) - 1)
                s["calls"].append(ok_subp[tmp]["name"])
                del ok_subp[tmp]

        # Read and write some variables. First we sprinkle the required
        # variables around.
        for v in req_vars:
            s = randint(0, len(p["sub"]) - 1)
            l = ("g_inputs"
                 if p["sub"][s]["kind"] == "function"
                 else choice(["g_inputs", "g_outputs"]))
            p["sub"][s][l].append(v)

        # Then we add some more
        for s_id, s in enumerate(p["sub"]):
            while True:
                l = ("g_inputs"
                     if p["sub"][s_id]["kind"] == "function"
                     else choice(["g_inputs", "g_outputs"]))
                v = choice(vis_vars + req_vars)
                s[l] = sorted(set(s[l]) | set([v]))
                if randint(1, 100) > EXTRA_VAR_USE_CHANCE:
                    break

    for i, p in enumerate(pack):
        emit_pkg(i)

if __name__ == "__main__":
    main()
