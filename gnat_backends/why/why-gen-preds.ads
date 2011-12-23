------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R E D S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Why.Ids;   use Why.Ids;
with Why.Sinfo; use Why.Sinfo;

package Why.Gen.Preds is

   --  This package provides facilities to manipulate Why predicates

   procedure Define_Range_Predicate
     (File      : W_File_Id;
      Name      : String;
      Base_Type : EW_Scalar);
   --  Generate the definition of the range predicate for an abstract type
   --  whose base type is given in parameters. This predicate is True when
   --  the argument is in range First .. Last.

   procedure Define_Eq_Predicate
     (File      : W_File_Id;
      Name      : String;
      Base_Type : EW_Scalar);
   --  Generate the definition of the equality predicate for an abstract type
   --  whose base type is given in parameters. This predicate is True when
   --  conversions to base type are equal.

   function New_Equal_Bool
     (Left  : W_Term_Id;
      Right : W_Pred_Id) return W_Pred_Id;
   --  Create the formula "Left = true <-> Right".

end Why.Gen.Preds;
