
def to_set(e):
    if e is None:
        # return set([])
        return set([])
    elif isinstance(e, set):
        return e
    elif isinstance(e, basestring):
        return { e }
    elif isinstance(e, (list,tuple,dict)):
        return set(e)
    else:
        return { e }

def to_list(e):
    if e is None:
        return []
    elif isinstance(e, list):
        return e
    elif isinstance(e, (basestring,dict)):
        return [ e ]
    elif isinstance(e, (set,tuple)):
        return list(e)
    else:
        return { e }

def to_dict(e):
    if e is None:
        return {}
    elif isinstance(e, dict):
        return e
    elif isinstance(e, basestring):
        return { e : None }
    elif isinstance(e, (list,tuple,set)):
        result = {}
        for key in e:
            result += { key : None }
        return result
    else:
        return { e : None }

def to_string(e):
    if e is None:
        return ""
    elif isinstance(e, dict):
        result = ["%s => %s" % (key, e[key]) for key in e]
        return ", ".join(result)
    elif isinstance(e, basestring):
        return e
    elif isinstance(e, (list,tuple,set)):
        result = [key for key in e]
        return ", ".join(result)
    else:
        return str(e)
