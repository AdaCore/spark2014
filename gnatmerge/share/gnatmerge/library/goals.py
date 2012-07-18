
from internal.conversions import to_string

class Goal:
    def __init__ (self, entity, value):
        self.entity = entity
        self.value = value

    def print_errors(self):
        entity = self.entity
        goal = self.value
        attribute = entity.object.attributes[entity.status_name()]

        for elt in entity.object.content():
            value = entity.object.follow(entity.status_name(), elt)
            sloc = entity.slocs.to_string(entity.object, elt)
            if not attribute.value_less_than(goal, value):
                self.print_error(elt, sloc, value)

    def print_error(self, name, sloc, value):
        print "%s : goal not reached at %s (%s)" % (sloc, name,
                                                    to_string(value))
