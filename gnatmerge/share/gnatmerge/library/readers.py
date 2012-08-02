import re
from internal.attributes import lattices
import gpr

class Reader:
    """Abstract class for readers

    ATTRIBUTES
      states: state domain targetted by the reader
    """

    def __init__(self, name):
        self.name = name
        self.filenames = []

    def load(self, filename):
        self.filenames.append(filename)

class TristateReader(Reader):

    def __init__(self, name):
        self.fragments = lattices.PartialOrderAttribute(name + ".STATUS",
                                                     {"OK", "KO"})
        # ??? name appended to make that attribute unique. Is that needed?
        self.fragments.name_and("PARTIAL OK", {"OK", "KO"})
        Reader.__init__(self, name)

class Listing(TristateReader):

    def iterate(self, proc):
        for filename in self.filenames:
            with open(filename) as f:
                lines = f.readlines()
                index = 1
                for line in lines:
                    element = {"MESSAGE" : line,
                               "NAME" : "%s%d" % (self.name, index)}
                    element = self.read_element(element, line)
                    if element is not None:
                        proc(element)
                    index += 1

    def read_element(self, element, line):
        return element

class ErrorListing(Listing):
    def __init__(self, name, ok_pattern="info", ignore_pattern=None):
        # ??? Use maps instead of patterns? Systematic use of merges?
        # if ok_pattern is a string, would this mean
        # {"OK" : ok_pattern, "KO" : others}?
        self.ok_pattern = ok_pattern
        self.ignore_pattern = ignore_pattern
        Listing.__init__(self, name)

    def read_element(self, element, line):
        if self.ignore_pattern is not None \
          and re.search(self.ignore_pattern, line) is not None:
            return None

        parts = line.split(":")
        if len(parts) < 3:
            print "warning: line with no sloc info: '%s'" % line.strip()
            return None
        sloc = parts[0] + ":" + parts[1] + ":" + parts[2]
        element["SLOCS"] = {"LOW" : sloc, "HIGH" : sloc}
        element[self.name + ".STATUS"] = self.read_status(line)
        # ??? name appended to make that attribute unique. Is that needed?
        return element

    def read_status(self, line):
        if self.ok_pattern is not None \
          and re.search (self.ok_pattern, line) is not None:
            return "OK"
        else:
            return "KO"

class AsisTreeReader(Reader):
    def __init__(self, name, sloc_domain, ename, maps):
        self.index = 0
        self.name = name
        self.fragments = sloc_domain
        self.ename = ename
        self.maps = maps
        Reader.__init__(self, name)
        self.sloc_reader = gpr.SlocReader()
        # ??? rename module gpr... Improper name
        for kind in maps:
            for asis_name in maps[kind]:
                self.sloc_reader.map_to_kind(asis_name, kind)

    def build_element(self, kind, name, low, high):
        slocs = {"LOW" : low, "HIGH" : high}
        element = {"KIND" : kind,
                   self.ename : name,
                   "NAME" : self.name + str(self.index) + "." + name,
                   "SLOCS" : slocs}
        self.index += 1
        return element

    def iterate(self, proc):
        index = 1
        for filename in self.filenames:
            self.index = 0
            self.sloc_reader.iterate(filename,
                                     lambda kind, name, low, high:
                                     proc(self.build_element(kind, name,
                                                             low, high)))
        return None
