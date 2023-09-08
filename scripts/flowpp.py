# This file contains GDB pretty-printers for types used in flow analysis.
# To enable them just add a line like this to your ~/.gdbinit:
# source ~/adacore/spark2014/scripts/flowpp.py

import gdb


class EntitynamePrinter:
    """Pretty-printer for Entity_Name datatype"""

    # The constructor takes the value and stores it for later

    def __init__(self, val):
        self.val = val

    def display_hint(self):
        return "string"

    def to_string(self):
        # First get the underlying integer and then simulate the
        # Common_Containers.To_String function, which queries an internal
        # vector object.

        id = int(self.val)
        symb = gdb.parse_and_eval("string_cache.elements.ea[" + str(id) + "]")
        name = str(symb)
        assert name[0] == '"' and name[-1] == '"'
        return str(name).strip('"')


# Next, define the lookup function that returns the printer object when it
# receives an object of a given type. The function takes a GDB value-type.
#
# ??? When printing containers with Entity_Name, e.g. Name_Sets, gdb thinks
# that the type of the element is Element_Type, which is actually a generic
# formal parameter of the container. Perhaps there is some way to get the
# actual type from the gdb.Value object, like there is for C/C++ typedefs?


def entityname_pp_func(val):
    val_type = str(val.type)
    if (
        val_type == "common_containers.entity_name"
        or val_type == "common_containers.name_sets.element_type"
        or val_type == "flow_generated_globals.phase_2.entity_contract_maps.key_typeXn"
    ):
        return EntitynamePrinter(val)


# Finally, append the pretty-printer as object/function to the list of
# registered GDB printers.


gdb.pretty_printers.append(entityname_pp_func)
