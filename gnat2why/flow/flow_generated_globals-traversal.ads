------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                    Copyright (C) 2016, Altran UK Limited                 --
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
------------------------------------------------------------------------------

package Flow_Generated_Globals.Traversal is

   procedure Build_Tree (CU : Node_Id);
   --  Traverse compilation unit CU to build a traversal tree

   procedure Dump_Tree;

   subtype Container_Scope is Entity_Kind
     with Static_Predicate => Container_Scope in Entry_Kind       |
                                                 E_Function       |
                                                 E_Package        |
                                                 E_Procedure      |
                                                 E_Protected_Type |
                                                 E_Task_Type;
   --  ??? subtype from Checked_Entity_Id

   function Root_Entity return Entity_Id
   with Post => No (Root_Entity'Result)
                  or else
                Ekind (Root_Entity'Result) in Container_Scope;
   --  Returns a cursor for the root scope; for custom iteration

   function Is_Leaf (E : Entity_Id) return Boolean;
   --  Returns True iff E is a leaf of the traversal tree

   generic
      with procedure Process (E : Entity_Id);
   procedure Fold0 (E : Entity_Id)
   with Pre => Ekind (E) in Container_Scope;

   generic
      type Context (<>) is limited private;
      with procedure Process (E   :        Entity_Id;
                              Ctx : in out Context);
   procedure Fold1 (E   :        Entity_Id;
                    Ctx : in out Context)
   with Pre => Ekind (E) in Container_Scope;

   generic
      type Context1 (<>) is limited private;
      type Context2 (<>) is limited private;
      with procedure Process (E    :        Entity_Id;
                              Ctx1 :        Context1;
                              Ctx2 : in out Context2);
   procedure Fold2 (E    :        Entity_Id;
                    Ctx1 :        Context1;
                    Ctx2 : in out Context2)
   with Pre => Ekind (E) in Container_Scope;

   generic
      type Context1 (<>) is limited private;
      type Context2 (<>) is limited private;
      type Context3 (<>) is limited private;
      with procedure Process (E    :        Entity_Id;
                              Ctx1 :        Context1;
                              Ctx2 :        Context2;
                              Ctx3 : in out Context3);
   procedure Fold3 (E    :        Entity_Id;
                    Ctx1 :        Context1;
                    Ctx2 :        Context2;
                    Ctx3 : in out Context3)
   with Pre => Ekind (E) in Container_Scope;

   --  Call Process on each scope nested in E; first on packages, then on
   --  subprograms.

   procedure Iterate_Main_Unit
     (Process : not null access procedure (E : Entity_Id));
   --  Iterate over scopes of the main unit in bottom-up fashion

   function Parent_Scope (E : Entity_Id) return Entity_Id
   with Pre  => Ekind (E) in Container_Scope,
        Post => Ekind (Parent_Scope'Result) in Container_Scope;
   --  Returns the parent scope of E (in the flow nesting sense)

end Flow_Generated_Globals.Traversal;
