"""
This module contains utility functions for both the testsuite and running
GNATprove on examples in the User's Guide.
"""


def sort_key_for_errors(line):
    """given a line of output, return a key that can be used for sorting

    if the line is of the form "file:line:col:msg", then the key is a tuple
    (file, line, col, rest), where file and rest are strings, and line and
    col are integers for correct sorting.
    [typical case of error messages]

    if the line is of the form "file:line", then the key is a tuple (file,
    line), where file is a string and line is an integer for correct sorting.
    [case of program traces]

    if the line is of the form "compilation of file failed", then the key
    is "zzzfile", to be bigger than most other strings of the previous kind,
    completed to a dummy tuple

    otherwise the key is a constant string which is bigger than most other
    strings, completed to a dummy tuple

    """
    sl = line.split(':', 3)
    if len(sl) == 4:
        try:
            return (sl[0], int(sl[1]), int(sl[2]), sl[3])
        except ValueError:
            return ("zzzzz", 0, 0, line)
    elif len(sl) == 2:
        try:
            return (sl[0], int(sl[1]))
        except ValueError:
            return ("zzzzz", 0, 0, line)
    else:
        sl = line.lstrip(' ').split(' ', 3)
        if len(sl) == 4 and sl[0] == "compilation" and sl[1] == "of":
            return ("zzz" + sl[2], 0, 0, line)
        else:
            return ("zzzzz", 0, 0, line)
