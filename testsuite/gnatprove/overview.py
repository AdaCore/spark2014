#!/usr/bin/env python

# Small script to print a count the tests in the testsuite, including large
# tests, totals of skipped and xfailed tests, by platform.

import os
import os.path

tests = os.listdir("tests")

print "Total number of tests: " + str(len(tests))

test_opt = 0
large = 0


class Platform:
    def __init__(self):
        self.qualifiers = set()
        self.xfail = 0
        self.skip = 0
        self.dead = 0

    def match(self, s):
        tags = s.split(',')
        for q in tags:
            if q not in self.qualifiers:
                return False
        return True

    def add_xfail(self):
        self.xfail += 1

    def add_skip(self):
        self.skip += 1

    def add_dead(self):
        self.dead += 1


class AllPlatforms(Platform):
    def __init__(self):
        Platform.__init__(self)
        self.name = "all platforms"
        self.qualifiers.add("ALL")


class X86Windows(Platform):
    def __init__(self):
        Platform.__init__(self)
        self.name = "x86-windows"
        self.qualifiers.add("32bits")
        self.qualifiers.add("NT")
        self.qualifiers.add("Windows")


class X8664Darwin(Platform):
    def __init__(self):
        Platform.__init__(self)
        self.name = "x86_64-darwin"
        self.qualifiers.add("Darwin")
        self.qualifiers.add("64bits")


class X8664Linux(Platform):
    def __init__(self):
        Platform.__init__(self)
        self.name = "x86_64-linux"
        self.qualifiers.add("linux")
        self.qualifiers.add("64bits")


platforms = [AllPlatforms(), X86Windows(), X8664Darwin(), X8664Linux()]

for test in tests:
    try:
        with open(os.path.join("tests", test, "test.opt"), 'r') as fn:
            test_opt += 1
            for line in fn.readlines():
                if line.startswith("!large SKIP"):
                    large += 1
                elts = line.split(' ')
                if len(elts) < 2:
                    continue
                if elts[1] == "RLIMIT":
                    continue
                if elts[1] == "TIMING":
                    continue
                if elts[1] == "XFAIL":
                    for p in platforms:
                        if p.match(elts[0]):
                            p.add_xfail()
                if elts[1] == "SKIP":
                    for p in platforms:
                        if p.match(elts[0]):
                            p.add_skip()
                if elts[1] == "DEAD":
                    for p in platforms:
                        if p.match(elts[0]):
                            p.add_dead()
    except IOError:
        pass

print "Large tests: " + str(large)
print "Tests with a test.opt: " + str(test_opt)

for p in platforms:
    print "Tests XFAILed on " + p.name + ": " + str(p.xfail)
    print "Tests SKIPped on " + p.name + ": " + str(p.skip)
    print "Tests DEAD on " + p.name + ": " + str(p.dead)
