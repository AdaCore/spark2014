
class Listing:

    def __init__(self, prefix, filename):
        self.prefix = prefix
        self.filename = filename

    def iterate(self, proc):
        with open(self.filename) as f:
            lines = f.readlines()
            index = 1
            for line in lines:
                element = {}
                parts = line.split(":")
                sloc = parts[0] + ":" + parts[1] + ":" + parts[2]
                element["SLOCS"] = {"LOW" : sloc, "HIGH" : sloc}
                if "info" in line:
                    element["STATUS"] = "OK"
                else:
                    element["STATUS"] = "KO"
                element["NAME"] = "%s%d(%s)" % (self.prefix, index, sloc)
                proc(element)
                index += 1
