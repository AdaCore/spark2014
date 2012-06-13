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
        self.states.name_meet("PARTIAL OK", {"OK", "KO"})
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
                    proc(element)
                    index += 1

    def read_element(self, element, line):
        return element

class ErrorListing(Listing):
    def read_element(self, element, line):
        parts = line.split(":")
        sloc = parts[0] + ":" + parts[1] + ":" + parts[2]
        element["SLOCS"] = {"LOW" : sloc, "HIGH" : sloc}
        element[self.name + ".STATUS"] = "OK" if "info" in line else "KO"
        # ??? name appended to make that attribute unique. Is that needed?
        return element
