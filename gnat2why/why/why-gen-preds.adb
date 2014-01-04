------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R E D S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Why.Conversions;     use Why.Conversions;

package body Why.Gen.Preds is

   --------------------
   -- New_Equal_Bool --
   --------------------

   function New_Equal_Bool
     (Left  : W_Term_Id;
      Right : W_Pred_Id) return W_Pred_Id
   is
   begin
      return
        New_Connection
          (Op    => EW_Equivalent,
           Left  =>
             New_Relation
               (Domain  => EW_Prog,
                Op      => EW_Eq,
                Op_Type => EW_Bool,
                Left    => +Left,
                Right   => New_Literal (Value => EW_True, Domain => EW_Prog)),
           Right => +Right);
   end New_Equal_Bool;

end Why.Gen.Preds;
