"""This package provides the basic API to interface tools with gnatmerge
"""

from internal.attributes import lattices

slocs_attribute = lattices.RangeAttribute(lattices.Sloc,
                                          "SLOCS", "LOW", "HIGH")
tristate_attribute = lattices.PartialOrderAttribute("STATUS", {"OK", "KO"})
tristate_attribute.name_meet("PARTIAL OK", {"OK", "KO"})

def slocs():
    """Return the range attribute used to represent source lines of codes"""
    global slocs_attribute
    return slocs_attribute

def tristate():
    """Return the attribute used to represent a tristate result of a tool

    The three possible status are:
    * OK: all sub-entities are OK;
    * KO: all sub-entities are KO;
    * PARTIAL OK: some sub-entities are OK, some are KO"""
    global tristate_attribute
    return tristate_attribute


