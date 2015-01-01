------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - G E N - T E R M S                    --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with Why.Ids;            use Why.Ids;
with Why.Types;          use Why.Types;
with Why.Sinfo;          use Why.Sinfo;
with Common_Containers;  use Common_Containers;
with Why.Atree.Builders; use Why.Atree.Builders;

package Why.Gen.Terms is
   --  Functions that deal with generation of terms

   True_Term  : constant W_Term_Id := New_Literal (Value => EW_True);
   False_Term : constant W_Term_Id := New_Literal (Value => EW_False);

   function Get_All_Dereferences (W : Why_Node_Id) return Node_Sets.Set;
   --  Return a list of the variables dereferenced in T

   function Has_Dereference_Or_Any (T : W_Term_Id) return Boolean;
   --  Return True if T contains a dereference

   function New_Ifb (Condition, Left, Right : W_Term_Id) return W_Term_Id;
   --  Build a if-then-else construct with a boolean test and terms in the
   --  branches.

   function New_Old (Expr : W_Expr_Id; Domain : EW_Domain) return W_Expr_Id;
   --  Build the expression old Expr

end Why.Gen.Terms;
