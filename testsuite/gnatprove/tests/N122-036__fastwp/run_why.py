#!/usr/bin/env python

import tools
import sys

def main():
    tools.print_list (tools.run_why (sys.argv[1], []))


if __name__ == "__main__":
    main()
