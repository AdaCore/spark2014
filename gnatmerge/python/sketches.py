
class PartialOrder:
    def __init__(self, objects):
        self.objects = {}
        self.weaker_classes = {}

    def assume_stronger(self, left, right):
        # add left > right
        if self.weaker_classes.has_key(left):
            self.weaker_classes[left].append(left)
        else:
            self.weaker_classes[left] = [right,]

        # compute transitive closure
        for key in self.weaker_classes:
            if left in self.weaker_classes[key]:
                self.weaker_classes[key].append(right)

def _arrow(name, domain, codomain, operation):
    return {"domain"    : domain,
            "codomain"  : codomain,
            "name"      : name,
            "operation" : operation}

def dict_append(dictionary, key, element):
    if dictionary.has_key(key):
        dictionary[key].append(element)
    else:
        dictionary[key] = [element,]

def arrow_to_string(arrow):
    return arrow["name"] + " : " + arrow["domain"] + " -> " + arrow["codomain"]

class FiniteSketch:
    def __init__(self, objects):
        self.objects = {}
        self.arrows_by_domain = {}
        self.arrows_by_codomain = {}

    def add_monic(self, domain, codomain, name=None):
        return self.add_arrow(domain, codomain, name, None)

    def _add_arrows_in_dicts(self, arrow):
        dict_append(self.arrows_by_domain, arrow["domain"], arrow)
        dict_append(self.arrows_by_codomain, arrow["codomain"], arrow)

    def _compose_ops(self, left, right):
        if left is None:
            return right
        elif right is None:
            return left
        else:
            return [left, right]

    def _compose_and_add(self, left, right):
        assert(left["codomain"] == right["domain"])
        new_arrow = _arrow(left["name"] + "." + right["name"],
                           left["domain"],
                           right["codomain"],
                           self._compose_ops(left["operation"],
                                             right["operation"]))
        self._add_arrows_in_dicts(new_arrow)
        return new_arrow


    def add_arrow(self, domain, codomain, name=None, operation=None):
        if name is None:
            name = domain + "_to_" + codomain

        result = _arrow(name, domain, codomain, operation)
        self._add_arrows_in_dicts(result)

        # Produce new arrows by composition
        added_arrows = [result]
        if self.arrows_by_codomain.has_key(domain):
            for arrow in self.arrows_by_codomain[domain]:
                new_arrow = self._compose_and_add(arrow, result)
                added_arrows.append(new_arrow)
        if self.arrows_by_domain.has_key(codomain):
            for arrow in self.arrows_by_domain[codomain]:
                for just_added in added_arrows:
                    self._compose_and_add(just_added, arrow)

        return result

    def execute(operation, operand, realization=None):
        if operation is None:
            return operand
        elif isinstance(operation, basestring):
            if realization is not None:
                return realization[operation](operand)
            else:
                return operand
        elif isinstance(operand, dict):
            return execute(operation["operation"], operand)
        elif isinstance(operand, list):
            return execute(operation[1:], execute(operation[0], operation))
        else:
            return operation(operand)
