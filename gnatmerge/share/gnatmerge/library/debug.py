"""Decorators for debug traces

This provides a couple of decorators (log_function, log_method) to be
used for configuring debug traces. Logging is conditioned by a configuration
file that contains a list of patterns. When a function matches a pattern,
its calls, parameters and results are logged. The syntax of a pattern may
be found in the function log.
"""

from utils import full_str
import gpr

log_list = None
log_offset = 0

def match_name(pattern, name):
    """Simple match

    This implements the match for a simple name; that is unqualified.
    Pattern is either a simple name as well, or '*'.
    """
    return pattern == '*' or name == pattern

def indent_log(offset):
    """Increase/decreate the indentation by offset
    """
    global log_offset
    log_offset += offset

def print_log(message):
    """Print message with the current indentation offset
    """
    print ' ' * log_offset + message

def log_list_entry(function_name, module_name, max_length):
    """First entry in the log list matching the parameters, None if none

    PARAMETERS
      function_name: name of the actual function/method to match
      module_name: name of the actual module to match
      max_length: maximum number of parts in the log list pattern.
                  e.g 2 for functions ([module, function]),
                      3 for methods   ([module, class, function])
    """
    if log_list is None:
        return None
    for to_log in log_list:
        if len(to_log) < max_length:
            if match_name (to_log[-1], function_name):
                return to_log
        else:
            if (match_name(to_log[-1], function_name)
                and match_name(to_log[0], module_name)):
                return to_log
    return None

def log_function(f):
    """Decorator for function logging

    Allow to log the function call when a matching pattern is found in the
    log list.
    """
    name = f.__name__
    match = log_list_entry(name, f.__module__, 2)

    if match is None:
        return f

    def wrapper(*args, **kwargs):
        args_str = ", ".join([full_str(arg) for arg in args])
        print_log('%s(%s)' % (name, args_str))
        indent_log(+1)
        ret = f(*args, **kwargs)
        indent_log(-1)
        print_log('%s returns %s' % (name, full_str(ret)))
        return ret

    return wrapper

def log_method(f):
    """Decorator for method logging

    Same as log_function, but for methods.
    """
    name = f.__name__
    match = log_list_entry(name, f.__module__, 3)

    if match is None:
        return f

    if len(match) > 1:
        class_name = match[-2]
    else:
        class_name = None

    def wrapper(self, *args, **kwargs):
        if (class_name is not None
            and not match_name(class_name, self.__class__.__name__)):
            return f(self, *args, **kwargs)

        args_str = ", ".join([full_str(arg) for arg in self, args])
        print_log('%s(%s)' % (name, args_str))
        indent_log(+1)
        ret = f(self, *args, **kwargs)
        indent_log(-1)
        print_log('%s returns %s' % (name, full_str(ret)))
        return ret

    return wrapper

def log(to_log):
    """Register a pattern for functions/methods to be logged

    PARAMETERS
      to_log: pattern. 2 kinds of them:

              - function pattern: those are of the form:
                [<module_name> '.'] <function_name>
              - method pattern: those are of the form:
                [[<module_name> '.'] <class_name> '.' ] <function_name>

              ...<module_name>, <class_name> and <function_name> can
              be either a name, or '*' (meaning "any").
              [<part>] designating an optional <part> here.
    """
    global log_list
    if log_list is None:
        log_list = []
    log_list.append(to_log.split('.'))

def load_config_file(filename):
    """load a configuration file
    """
    with open(filename) as f:
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if line != '' and line[0] != '#':
                log(line)

def main():
    """Load the configuration file of debug traces

    Note that this has to be done before any log decorator;
    the best way to achieve that is to make that happen as soon
    as module debug is imported.
    """
    if log_list is None:
        debug_conf = gpr.debug_conf()
        if debug_conf != '':
            load_config_file(debug_conf)

main()
