------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   C E _ P R E T T Y _ P R I N T I N G                    --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                    Copyright (C) 2018-2018, AdaCore                      --
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

package Ce_Pretty_Printing is

   function StringBits_To_Approx (Sign, Significand, Exp : String)
                                  return String;
   --  This function takes the three (sign, mantissa and exponent) string of
   --  bits representation output by prover and uses standard Ada float_io to
   --  output a decimal representation with 10 significant digits for 64bit
   --  float and 7 significant digits for 32 bits float.

end Ce_Pretty_Printing;
