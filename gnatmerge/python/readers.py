
class Listing:

    def __init__(self, prefix, filename):
        self.prefix = prefix
        self.filename = filename

    def iterate(self, proc):
        with open(self.filename) as f:
            lines = f.readlines()
            index = 1
            for line in lines:
                element = {"MESSAGE" : line,
                           "NAME" : "%s%d" % (self.prefix, index)}
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
        element["STATUS"] = "OK" if "info" in line else "KO"
        return element
