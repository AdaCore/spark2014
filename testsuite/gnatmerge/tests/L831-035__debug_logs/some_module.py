from debug import log_method, log_function

class SomeClass:
    @log_method
    def __init__(self):
        self.my_int = 1000000
    
    @log_method
    def traced_method(self, i):
        self.my_int += i
        return self.my_int

    @log_method
    def untraced_method(self, i):
        self.my_int += i
        return self.my_int

    def __str__(self):
        if "i" in dir(self):
            i = "%d" % self.i
        else:
            i = "NaN"
        return "<SomeClass> %s" % i

@log_function
def some_tracked_function(i):
    s = SomeClass()
    s.traced_method(i + 1)
    s.untraced_method(i + 2)
    return s

@log_function
def some_untracked_function(i):
    s = SomeClass()
    s.traced_method(i + 3)
    s.untraced_method(i + 4)
    return s

some_tracked_function(1000)
some_untracked_function(2000)

