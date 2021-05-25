import sys
import re

header = """\
------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     G N A T 2 W H Y - K E Y W O R D S                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2019-2021, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

"""

prelude = """with String_Utils; use String_Utils;

package body Why.Keywords is
   --  This file is automatically generated by scripts/why3keywods.py

   procedure Update_Keywords (Keywords : out String_Utils.String_Sets.Set) is
   begin
      --  This part is automatically generated
"""

postlude = """
   end Update_Keywords;

end Why.Keywords;
"""

regexp = re.compile(".*\"([a-z]*)\", [A-Z]*;.*")


def find_keywords(input_file):
    result = ""
    update = '      Keywords.Insert ("'
    input_file = open(input_file, 'r')
    for line in input_file:
        x = re.search(regexp, line)
        if x is not None and x.group(1) is not None:
            result = result + (update + x.group(1) + '");\n')
    return result


f = open(sys.argv[2], 'w', newline='\n')

try:
    update = find_keywords(sys.argv[1])
except Exception:
    print("Generation of Keywords: Abort")
    print("Problem during the opening or parsing of lexer.mll")
    print("Please check you are in developper build")
    exit(1)

f.write(header + prelude + update + postlude)