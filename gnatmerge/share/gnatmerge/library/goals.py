
from internal.conversions import to_string

class Goal:
    def __init__ (self, entity, value):
        self.entity = entity
        self.value = value

    def print_errors(self, verbose=False):
        entity = self.entity
        goal = self.value
        attribute = entity.object.attributes[entity.status_attr_id()]

        for elt in entity.object.content():
            value = entity.object.follow(entity.status_attr_id(), elt)
            sloc = entity.spans.to_string(entity.object, elt)
            # ??? print sloc instead of span here...
            if not attribute.value_less_than(goal, value):
                self.print_error(elt, sloc, value)
            elif verbose:
                self.print_info(elt, sloc, value)

    def print_info(self, name, sloc, value):
        self.print_msg("info: goal reached", name, sloc, value)

    def print_error(self, name, sloc, value):
        self.print_msg("goal not reached", name, sloc, value)

    def print_msg(self, msg, name, sloc, value):
        print "%s: %s at %s (%s)" % (sloc, msg, name, to_string(value))
