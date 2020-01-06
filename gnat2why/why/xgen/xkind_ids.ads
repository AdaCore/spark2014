------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            X K I N D _ I D S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Outputs; use Outputs;

package Xkind_Ids is
   --  This package provides routines to generate node Id subtypes

   procedure Print_Derived_Types (O : in out Output_Record);
   --  ??? Should replace Print_Regular_Subtypes at some point.
   --  See comment of Xkind_Tables.Id_Kind.

   procedure Print_Regular_Subtypes (O : in out Output_Record);
   --  Expand the kind-specific subtype declarations of Why_Node_Id
   --  and Why_Node_List. To each subtypes a predicate is associated
   --  that assert that the corresponding element in the node table is
   --  the root of a valid Why syntax tree.
   --  Same thing for classes.

   procedure Print_Unchecked_Subtypes (O : in out Output_Record);
   --  Same as Print_Subtypes, except that the expanded subtype will only
   --  be checked for kind-validity. e.g. a W_Type_Id always point to an
   --  element of kind W_Type in the node table; and W_Type_List contains only
   --  elements of kind W_Type.

   procedure Print_Opaque_Subtypes (O : in out Output_Record);
   --  Same as Print_Subtypes, except that the expanded subtype declarations
   --  will have no subtype predicate; (e.g. W_Type_Opaque_Id and
   --  W_Type_Opaque_List for kind W_Type).

end Xkind_Ids;
