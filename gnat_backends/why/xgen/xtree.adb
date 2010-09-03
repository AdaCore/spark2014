------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                               X K I N D S                                --
--                                                                          --
--                                 B o d y                                  --
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

with Xtree_Load;      use Xtree_Load;
with Xtree_Builders;  use Xtree_Builders;
with Xtree_Accessors; use Xtree_Accessors;
with Xtree_Mutators;  use Xtree_Mutators;
with Xtree_Traversal; use Xtree_Traversal;
with Templates;       use Templates;

procedure Xtree is
   --  ASIS helper that takes Why.Atree's syntax tree and generates
   --  builders, accessors/mutators, recursive traversal...

begin
   Load_Atree;

   --  Production of packages for builders, accessors, mutators

   Add ("Declare_Builders", Print_Builder_Declarations'Access);
   Add ("Declare_Unchecked_Builders",
        Print_Unchecked_Builder_Declarations'Access);
   Add ("Implement_Builders", Print_Builder_Bodies'Access);
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

   Process ("why-atree-builders.ads");
   Process ("why-atree-builders.adb");
   Process ("why-atree-accessors.ads");
   Process ("why-atree-mutators.ads");
   Process ("why-atree-mutators.adb");
   Process ("why-atree-traversal.ads");
   Process ("why-atree-traversal.adb");
   Process ("why-atree-traversal_stub.ads");
   Process ("why-atree-traversal_stub.adb");
end Xtree;
