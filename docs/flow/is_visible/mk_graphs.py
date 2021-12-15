#!/usr/bin/env python

PARTS = ("spec", "priv", "body")


class Flow_Scope(object):
    def __init__(self, name, part="spec"):
        assert name is None or type(name) is str
        assert part in PARTS

        self.name = name
        self.part = part


class Enclosure_Info(object):
    def __init__(self, name, parent=None):
        self.name = name

        self.is_generic = False

        self.is_private = False
        self.is_instance = False
        self.is_nested = False

        self.parent = parent
        self.template = None
        self.container = Flow_Scope(None)

    def is_child(self):
        return (
            not self.is_private
            and not self.is_nested
            and self.parent not in (None, "standard")
        )

    def tex_name(self):
        return self.name.lower().replace(".", " ")

    def to_vertex(self):
        n = self.tex_name()

        if n == "standard":
            opts = "blue,root,"
        elif self.is_generic:
            opts = "brown,"
        else:
            opts = ""

        rv = ""
        for part in PARTS:
            rv += "%s %s [%sas=%s (%s)];\n" % (
                n,
                part,
                opts,
                self.name,
                part.capitalize(),
            )
            if n == "standard":
                break
        return rv

    def to_graph(self, mapping):
        n = self.tex_name()

        rv = ""

        if n == "standard":
            return rv

        # Rule 0
        rv += "%s body -> %s priv -> %s spec;\n" % (n, n, n)

        # Rule 1
        rv += "%s spec -> " % n
        if self.is_instance:
            rv += "%s spec" % self.template
        elif self.is_nested:
            rv += "%s %s" % (self.container.name, self.container.part)
        elif self.is_private:
            rv += "%s priv" % self.parent
        else:
            rv += "%s spec" % self.parent
        rv += ";\n"

        # Rule 2
        rv += "%s spec <- " % n
        if self.is_nested:
            rv += "%s %s" % (self.container.name, self.container.part)
        elif self.is_private:
            rv += "%s priv" % self.parent
        else:
            rv += "%s spec" % self.parent
        rv += ";\n"

        # Rule 3
        if self.is_instance:
            rv += "%s priv -> %s priv;\n" % (n, self.template)
        elif self.is_child():
            rv += "%s priv -> %s priv;\n" % (n, self.parent)

        # Rule 4
        if self.is_instance:
            rv += "%s body -> %s body;\n" % (n, self.template)
        elif self.is_nested:
            rv += "%s body -> %s body;\n" % (n, self.container.name)

        return rv

    def child(self, parent):
        self.parent = parent
        return self

    def pchild(self, parent):
        self.is_private = True
        self.parent = parent
        return self

    def nested(self, enclosure, part):
        self.is_nested = True
        self.container.name = enclosure
        self.container.part = part
        self.parent = None
        return self

    def generic(self):
        self.is_generic = True
        return self

    def instance(self, template):
        self.is_instance = True
        self.template = template
        return self


def create_map(enclosures):
    info = {}
    for e in enclosures:
        info[e.tex_name()] = e
    return info


standard = Enclosure_Info("Standard")


def emit_figure(fd, enclosures, caption):
    info = create_map(enclosures)

    fd.write("\\begin{figure}[h!t]\n")
    fd.write("\\begin{center}\n")
    fd.write("\\begin{tikzpicture}[rounded corners]\n")
    fd.write("\\graph[layered layout,node distance=2.5cm]{\n")

    for e in enclosures:
        fd.write(e.to_vertex())
    for e in enclosures:
        fd.write(e.to_graph(info))

    fd.write("};\n")
    fd.write("\\end{tikzpicture}\n")
    fd.write("\\end{center}\n")
    fd.write("\\caption{%s}\n" % caption)
    fd.write("\\end{figure}\n")


def fig1():
    lst = [
        standard,
        Enclosure_Info("Pkg").child("standard"),
        Enclosure_Info("Pkg.Child").child("pkg"),
        Enclosure_Info("Pkg.PChild").pchild("pkg"),
    ]

    with open("figure1.tex", "w") as fd:
        emit_figure(
            fd,
            lst,
            "A simple library-level package ``pkg'', along with"
            " a child ``pkg.child'' and a private child ``pkg.pchild''"
            ".",
        )


def fig2():
    lst = [
        standard,
        Enclosure_Info("Coll").child("standard"),
        Enclosure_Info("Coll.Gen").child("coll").generic(),
        Enclosure_Info("Arrays").child("standard").instance("coll gen"),
        Enclosure_Info("Lists").child("standard").instance("coll gen"),
    ]

    with open("figure2.tex", "w") as fd:
        emit_figure(
            fd,
            lst,
            "An instantiation of a fictional ``coll.vectors'' package "
            "as the library level package ``lists'' and ``arrays''. "
            "In particular, the body of lists does not have visibility "
            "of the private part of arrays.",
        )


def fig3():
    lst = [
        standard,
        Enclosure_Info("Pkg").child("standard"),
        Enclosure_Info("Gen").child("standard").generic(),
        Enclosure_Info("Inst").nested("pkg", "body").instance("gen"),
    ]

    with open("figure3.tex", "w") as fd:
        emit_figure(
            fd,
            lst,
            "Package ``pkg'' contains (in its body part) a nested "
            "instantiation ``inst'' of generic ``gen''. The body of "
            "the instantiation has no visibility over the package "
            "private part or body.",
        )


def fig4():
    lst = [
        standard,
        Enclosure_Info("Pkg").child("standard"),
        Enclosure_Info("Pkg.Nested").nested("pkg", "spec"),
    ]

    with open("figure4.tex", "w") as fd:
        emit_figure(
            fd,
            lst,
            "Package ``pkg'' contains (in its spec) a nested package "
            "package ``nested''. The private part of the nested "
            "package does not have visibility over the private part "
            "of the enclosing package, but its body does.",
        )


def fig5():
    lst = [
        standard,
        Enclosure_Info("Pkg").child("standard"),
        Enclosure_Info("Pkg.Gen").nested("pkg", "spec").generic(),
        Enclosure_Info("Pkg.Child").child("pkg").instance("pkg gen"),
    ]

    with open("figure5.tex", "w") as fd:
        emit_figure(
            fd,
            lst,
            "Package ``pkg'' contains a nested generic ``pkg.gen''. "
            "This generic is used to instantiate the package own child "
            "``pkg.child''. The body of this child does not have "
            "visibility of its parent private part, unlike a normal "
            "child.",
        )


fig1()
fig2()
fig3()
fig4()
fig5()
