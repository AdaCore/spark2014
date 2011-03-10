------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - G E N - T E R M S                    --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Why.Ids;   use Why.Ids;
with Why.Sinfo; use Why.Sinfo;

package Why.Gen.Terms is
   --  Functions that deal with generation of terms

   function New_Andb (Left, Right : W_Term_Id) return W_Term_Id;
   --  Build a boolean conjunction.

   function New_Orb (Left, Right : W_Term_Id) return W_Term_Id;
   --  Build a boolean disjunction.

   function New_Ifb (Condition, Left, Right : W_Term_Id) return W_Term_Id;
   --  Build a if-then-else construct with a boolean test and terms in the
   --  branches.

   function New_Boolean_Cmp (Cmp : W_Relation; Left, Right : W_Term_Id)
      return W_Term_Id;
   --  build a boolean comparison for terms of "int" type.
end Why.Gen.Terms;
