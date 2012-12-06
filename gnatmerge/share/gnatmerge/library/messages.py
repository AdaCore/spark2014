"""Representation of tool messages
"""

from utils import attr_str, full_str
from internal import conversions
from debug import log_method, log_function
from elements import elements_union, dicts_union

class Span:
    """Span of source code
    """

    @log_method
    def __init__(self, low, high):
        """Build a span of source code from its bounds

        PARAMETERS
          low: sloc at the begining of the span
          high: sloc at the end of the span
        """
        self.low = low
        self.high = high

    def __str__(self):
        """x.__str__() <==> str(x)"""
        low = attr_str(self, 'low')
        high = attr_str(self, 'high')
        return "%s-%s" % (low, high)

class Message:
    """Represent messages from tools

    Attributes are exactly the constructor's parameters.
    """

    @log_method
    def __init__(self, name=None, sloc=None, span=None, status=None,
                 message=None):
        """Constructor

        PARAMETERS
          name: unique label for this element
          sloc: source location associated to this message
          span: span of source code associated to this message
          status: original status associated to this message by its reader
          message: additional content
        """
        self.name = name
        self.sloc = sloc
        self.span = span
        self.status = status
        self.message = message

    def __str__(self):
        """x.__str__() <==> str(x)"""
        sloc = attr_str(self, 'sloc')
        message = attr_str(self, 'message')
        name = attr_str(self, 'name', " (name = %s)")
        status = attr_str(self, 'status', " (status = %s)")
        span = attr_str(self, 'span', " (span = %s)")
        return "<Message> %s: %s%s%s%s" % (sloc, message, name, status, span)

