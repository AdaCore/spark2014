from internal.attributes import lattices

class Reader:
    """Abstract class for readers

    ATTRIBUTES
      states: state domain targetted by the reader
    """

    def __init__(self, name):
        self.name = name
        self.states = lattices.PartialOrderAttribute(name + ".STATUS",
                                                     {"OK", "KO"})
        # ??? name appended to make that attribute unique. Is that needed?
        self.states.name_and("PARTIAL OK", {"OK", "KO"})
        self.filenames = []

    def load(self, filename):
        self.filenames.append(filename)

class Listing(Reader):

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
    def __init__(self, name, ok_pattern="info"):
        # ??? Use maps instead of patterns? Systematic use of merges?
        # if ok_pattern is a string, would this mean
        # {"OK" : ok_pattern, "KO" : others}?
        self.ok_pattern = ok_pattern
        Listing.__init__(self, name)

    def read_element(self, element, line):
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
        return "OK" if self.ok_pattern in line else "KO"
