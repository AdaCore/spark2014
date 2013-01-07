"""Various utility functions
"""

import types

def attr_str(object, attribute_name, format="%s"):
    """Formatted string for object.attribute_name

    ...object.attribute_name meaning object.__dict__[attribute_name] here.
    If attribute is not found or is None, returns an empty string.

    PARAMETERS
      object: object to dereference
      attribute_name: name of the attribute in object.
      format: format string, replace %s by object.attribute_name if
              attribute_name exists.
    """
    if attribute_name in dir(object):
        value = object.__dict__[attribute_name]
        if value is not None:
            return format % full_str(value)
    return ""

def full_str(value):
    """Recursive str"""
    if isinstance(value, set):
        return "{ %s }" % ', '.join([full_str(e) for e in value])
    elif isinstance(value, list):
        return "[%s]" % ', '.join([full_str(e) for e in value])
    elif isinstance(value, tuple):
        return "(%s)" % ', '.join([full_str(e) for e in value])
    elif isinstance(value, dict):
        return "{ %s }" % ', '.join(["%s : %s" % (k, full_str(value[k]))
                                     for k in value])
    else:
        return str(value)

def final_singleton(cls):
    """Singleton class decorator

    Make sure that the constructor always returns the same instance.
    The decorated class cannot be derived.
    """
    instances = {}
    def getinstance():
        if cls not in instances:
            instances[cls] = cls()
        return instances[cls]
    return getinstance
