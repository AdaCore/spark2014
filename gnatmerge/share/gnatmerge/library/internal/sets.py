import json
import conversions

class Arrow:
    def __init__(self):
        pass

    def follow(self, object, key):
        return key

class FunctionArrow(Arrow):
    def __init__(self, operation):
        self.operation = operation

    def follow(self, object, key):
        return self.operation(key, object.elements[key])

class FilteredArrow(Arrow):
    def __init__(self, arrow, maps):
        self.arrow = arrow
        self.maps = maps

    def follow(self, object, key):
        return self.maps[self.arrow.follow(object, key)]

class Object:
    def __init__(self, name):
        self.name = name
        self.elements = {}
        self.arrows = {}
        self.attributes = {}

    def add(self, key, value):
        self.elements[key] = value

    def follow_all_arrows(self, key):
        for a in self.arrows:
            self.elements[key][a] = self.arrows[a].follow(self, key)

    def content(self):
        return self.elements

    def follow(self, arrow, key):
        if arrow not in self.elements[key]:
            self.elements[key][arrow] = self.arrows[arrow].follow(self, key)

        return self.elements[key][arrow]

    def element(self,key):
        return self.elements[key]

    def new_arrow(self, name, operation):
        self.arrows[name] = operation

    def new_attribute(self, domain):
        """Add a new attribute to the object

        PARAMETERS
          domain: attribute domain, of class attributes.common.Attribute
        """
        self.attributes[domain.name] = domain
        self.new_arrow(domain.name, domain)

    def load_element(self, element):
        self.add(element["NAME"], element)

    def load(self, reader):
        reader.iterate(lambda x : self.load_element(x))

class Objects:
    def __init__(self):
        self.objects = {}

    def register_object(self, object):
        self.objects[object.name] = object

    def object(self, key):
        return self.objects[key]

    def loads(self, filename):
        with open(filename) as f:
            self.record(json.loads(f.read()))

    def new_object(self, name):
        result = Object(name)
        self.register_object(result)
        return result

    def record(self, input):
        for key in input:
            for element in input[key]:
                self.objects[key].add(element["NAME"], element)

