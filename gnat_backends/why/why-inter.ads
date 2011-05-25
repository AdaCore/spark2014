------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
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

with Ada.Containers;                     use Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;

with String_Utils;                       use String_Utils;
with Types;                              use Types;

package Why.Inter is
   --  This package contains types that are used to represent intermediate
   --  phases of the translation process.

   package List_Of_Nodes is new Doubly_Linked_Lists (Node_Id);
   --  Standard list of nodes. It is better to use these, as a Node_Id can be
   --  in any number of these lists, while it can be only in one List_Id.

   type Why_Package is
      record
         WP_Name    : access String;
         WP_Context : String_Lists.List;
         WP_Decls   : List_Of_Nodes.List;
      end record;
   --  This type represents a Why package (file), whose list of declarations
   --  is not yet translated. Such a package has a name, a list of packages to
   --  include and the list of Ada nodes yet to be translated.

   package List_Of_Why_Packs is new Doubly_Linked_Lists (Why_Package);

   function Make_Empty_Why_Pack (S : String) return Why_Package;
   --  Build an empty Why_Package with the given name

   procedure Add_With_Clause (P : out Why_Package; Name : String);
   --  Add a package name to the context of a Why package.

   procedure Add_With_Clause (P : out Why_Package; Other : Why_Package);
   --  Add a package name to the context of a Why package.

   type Why_Type_Enum is (Why_Int, Why_Abstract);
   type Why_Type (Kind : Why_Type_Enum := Why_Int) is
      record
         case Kind is
            when Why_Int =>
               null;
            when Why_Abstract =>
               Wh_Abstract : Node_Id;
         end case;
      end record;
   --  The type of Why types, as used by the translation process; A type in
   --  Why is either the builtin "int" type or a node that corresponds to a
   --  N_Defining_Identifier of an Ada type

   Why_Int_Type : constant Why_Type (Why_Int) := (Kind => Why_Int);
end Why.Inter;
