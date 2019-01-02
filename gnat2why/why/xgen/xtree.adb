------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                X T R E E                                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with Xkind_Decls;           use Xkind_Decls;
with Xkind_Ids;             use Xkind_Ids;
with Xkind_Checks;          use Xkind_Checks;
with Xkind_Conversions;     use Xkind_Conversions;
with Xtree_Sinfo;           use Xtree_Sinfo;
with Xtree_Decls;           use Xtree_Decls;
with Xtree_Builders;        use Xtree_Builders;
with Xtree_Accessors;       use Xtree_Accessors;
with Xtree_Mutators;        use Xtree_Mutators;
with Xtree_Traversal;       use Xtree_Traversal;
with Xtree_Checks;          use Xtree_Checks;
with Xtree_Children_Checks; use Xtree_Children_Checks;
with Templates;             use Templates;

procedure Xtree is
   --  Helper that takes Why.Sinfo/Why.Atree's syntax tree and generates
   --  builders, accessors/mutators, recursive traversal...

begin
   Build_AST;

   --  Production of packages for node kinds/classes/types

   Add ("Declare_Node_Classes", Print_Node_Classes'Access);
   Add ("Declare_Node_Type", Print_Node_Type'Access);

   Process ("why-classes.ads");
   Process ("why-atree.ads");

   --  Production of packages from the kind/class lists

   Add ("Declare_Node_Ids", Print_Regular_Subtypes'Access);
   Add ("Declare_Unchecked_Ids", Print_Unchecked_Subtypes'Access);
   Add ("Declare_Opaque_Ids", Print_Opaque_Subtypes'Access);
   Add ("Declare_Derived_Ids", Print_Derived_Types'Access);

   Process ("why-ids.ads");
   Process ("why-unchecked_ids.ads");
   Process ("why-opaque_ids.ads");

   Add ("Declare_Conversions", Print_Conversion_Declarations'Access);
   Add ("Implement_Conversions", Print_Conversion_Bodies'Access);

   Process ("why-conversions.ads");

   --  Production of packages for builders, accessors, mutators

   Add ("Declare_Class_Wide_Builders",
        Print_Class_Wide_Builder_Declarations'Access);
   Add ("Declare_Unchecked_Builders",
        Print_Unchecked_Builder_Declarations'Access);
   Add ("Implement_Class_Wide_Builders",
        Print_Class_Wide_Builder_Bodies'Access);
   Add ("Implement_Unchecked_Builders",
        Print_Unchecked_Builder_Bodies'Access);
   Add ("Declare_Accessors", Print_Accessor_Declarations'Access);
   Add ("Implement_Accessors", Print_Accessor_Bodies'Access);
   Add ("Declare_Mutators", Print_Mutator_Declarations'Access);
   Add ("Implement_Mutators", Print_Mutator_Bodies'Access);
   Add ("Declare_Traversal_Ops", Print_Traversal_Op_Declarations'Access);
   Add ("Implement_Traverse", Print_Traverse_Body'Access);
   Add ("Declare_Traversal_Op_Stubs",
        Print_Traversal_Op_Stub_Declarations'Access);
   Add ("Implement_Traversal_Op_Stubs",
        Print_Traversal_Op_Stub_Bodies'Access);
   Add ("Declare_Treepr_Traversals",
        Print_Treepr_Traversal_Op_Declarations'Access);
   Add ("Implement_Treepr_Traversals",
        Print_Treepr_Traversal_Op_Bodies'Access);

   Process ("why-atree-builders.ads");
   Process ("why-atree-builders.adb");
   Process ("why-atree-accessors.ads");
   Process ("why-atree-mutators.ads");
   Process ("why-atree-mutators.adb");
   Process ("why-atree-traversal.ads");
   Process ("why-atree-traversal.adb");
   Process ("why-atree-traversal_stub.ads");
   Process ("why-atree-traversal_stub.adb");
   Process ("why-atree-treepr.ads");
   Process ("why-atree-treepr.adb");

   --  Production of packages for validity checks

   Add ("Declare_Kind_Checks", Print_Kind_Checks_Declarations'Access);
   Add ("Implement_Kind_Checks", Print_Kind_Checks_Bodies'Access);
   Add ("Declare_Checks", Print_Checks_Declarations'Access);
   Add ("Implement_Checks", Print_Checks_Bodies'Access);
   Add ("Declare_Children_Checks", Print_Children_Checks_Declarations'Access);
   Add ("Implement_Children_Checks", Print_Children_Checks_Bodies'Access);

   Process ("why-kind_validity.ads");
   Process ("why-atree-validity.ads");
end Xtree;
