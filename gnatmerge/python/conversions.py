
def to_set(e):
    if e is None:
        return set([])
    elif isinstance(e, set):
        return e
    elif isinstance(e, basestring):
        return { e }
    elif isinstance(e, (list,tuple,dict)):
        return set(e)
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
    else:
        return { e : None }

