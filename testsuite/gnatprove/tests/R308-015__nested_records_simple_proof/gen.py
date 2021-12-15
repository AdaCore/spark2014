#!/usr/bin/env python

import random

random.seed(0)

types = []


def lookup(name):
    for t in types:
        if t["name"] == name:
            return t
    raise AssertionError()


def mk_name():
    return "Type_%u" % len(types)


def mk_random():
    kind = random.choice(
        [
            "int",
            # "arr",
            "rec",
        ]
    )
    if kind == "int":
        return mk_int()
    elif kind == "arr":
        return mk_arr()
    elif kind == "rec":
        return mk_rec()
    else:
        raise AssertionError()


def mk_int():
    name = mk_name()

    types.append(
        {
            "name": name,
            "kind": "int",
            "decl": "type %s is new Integer" % name,
            "init": "0",
        }
    )

    return name


def get_random_int(kind=None):
    int_types = [t["name"] for t in types if t["kind"] == "int"]
    if random.randint(1, 3) == 1 or len(int_types) == 0:
        return mk_int()
    else:
        return random.choice(int_types)


def get_random():
    names = [t["name"] for t in types]
    rec_names = [t["name"] for t in types if t["kind"] == "rec"]
    if random.randint(1, 4) == 1 or len(names) == 0:
        return mk_random()
    elif random.randint(1, 3) > 1 and len(rec_names) > 0:
        return random.choice(rec_names)
    else:
        return random.choice(names)


def mk_arr():
    index_name = get_random_int()
    element_name = get_random()

    name = mk_name()

    types.append(
        {
            "name": name,
            "kind": "arr",
            "decl": "type %s is array (%s) of %s" % (name, index_name, element_name),
            "init": "(others => %s)" % lookup(element_name)["init"],
        }
    )

    return name


def mk_rec():
    num_fields = random.randint(3, 8)

    fields = []
    for field_id in range(num_fields):
        t = random.randint(0, len(fields) + 2)
        if t < len(fields):
            t = fields[t]["type"]
        else:
            t = get_random()
        fields.append({"name": "Field_%u" % field_id, "type": t})

    name = mk_name()

    decl = "type %s is record\n" % name
    for f in fields:
        decl += "   %s : %s;\n" % (f["name"], f["type"])
    decl += "end record"

    types.append(
        {
            "name": name,
            "kind": "rec",
            "decl": decl,
            "init": "Create_%s" % name,
            "fld": fields,
        }
    )
    return name


for _i in range(5):
    mk_rec()


def emit_gen(typ, fd_spec, fd_body):
    decl = "function %s return %s" % (typ["init"], typ["name"])
    fd_spec.write(decl + "\n")
    fd_body.write(decl + "\n")

    fd_spec.write("with Global => null,\n")
    for id, field in enumerate(typ["fld"]):
        expr = "%s'Result.%s = %s" % (
            typ["init"],
            field["name"],
            lookup(field["type"])["init"],
        )
        post_line = "     Post   => "
        if id > 0:
            post_line = " " * len(post_line)
        post_line += expr
        if id < len(typ["fld"]) - 1:
            post_line += " and then"
        else:
            post_line += ";"
        fd_spec.write(post_line + "\n")
    fd_spec.write("\n")

    fd_body.write("is\n")
    fd_body.write("begin\n")
    for id, field in enumerate(typ["fld"]):
        expr = "%s => %s" % (field["name"], lookup(field["type"])["init"])
        post_line = "   return ("
        if id > 0:
            post_line = " " * len(post_line)
        post_line += expr
        if id < len(typ["fld"]) - 1:
            post_line += ","
        else:
            post_line += ");"
        fd_body.write(post_line + "\n")
    fd_body.write("end %s;\n" % typ["init"])
    fd_body.write("\n")


with open("p.ads", "w") as fd_spec:
    with open("p.adb", "w") as fd_body:
        fd_spec.write("package P is\n\n")
        fd_body.write("package body P is\n\n")

        for t in types:
            fd_spec.write(t["decl"] + ";\n\n")

            if t["kind"] == "rec":
                emit_gen(t, fd_spec, fd_body)

        fd_spec.write("end P;\n")
        fd_body.write("end P;\n")
