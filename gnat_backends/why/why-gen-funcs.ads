------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - F U N C S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
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
with Why.Types; use Why.Types;

package Why.Gen.Funcs is
   --  This package provides facilities to generate subprograms declarations
   --  in the program space and in the logic space.

   procedure Declare_Logic
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id);
   --  Create a logic declaration from Name and Arrows and append it
   --  to File. Name is inserted into the resulting syntax tree,
   --  Arrows is not; the spec of the logic declaration is created
   --  from it.

   procedure Declare_Logic_And_Parameters
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id;
      Pre    : W_Predicate_OId := Why_Empty;
      Post   : W_Predicate_OId := Why_Empty);
   --  Create a logic declaration and it corresponding declaration in
   --  the program space (safe and default) and append it to File. Name
   --  is the name of the logic function declaration, Arrows is the
   --  spec of the default program declaration; all params will be merged
   --  as is into the resulting syntax tree.

   procedure Declare_Parameter
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id;
      Pre    : W_Predicate_OId := Why_Empty;
      Post   : W_Predicate_OId := Why_Empty);
   --  Create a subprogram declaration in the program space (a so called
   --  "parameter") from its name (Name) and its signature (Arrows). All
   --  parameters will be inserted as is into the resulting syntax tree.

end Why.Gen.Funcs;
