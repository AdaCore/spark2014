------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                   F L O W . D Y N A M I C _ M E M O R Y                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                   Copyright (C) 2019, Altran UK Limited                  --
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

with Namet;       use Namet;
with Nlists;      use Nlists;
with Nmake;       use Nmake;
with Sinfo;       use Sinfo;
with Snames;      use Snames;
with Stand;       use Stand;

package body Flow.Dynamic_Memory is

   Dynamic_Memory_Name : constant String := "dynamic_memory";
   Heap_Pkg_Name       : constant String := "heap";
   --  Literals for the "SPARK.Heap.Dynamic_Memory" abstract state (except for
   --  "SPARK", because its Name_Id is predefined in the fronend).

   Dynamic_Memory_Id : Entity_Id := Empty;
   --  An entity for the abstract state that represents memory (de)allocation.
   --  It should be considered a constant; however, we cannot create it at
   --  elaboration, because we need to wait until node tables are ready.

   -----------------------
   -- Create_Heap_State --
   -----------------------

   procedure Create_Heap_State is
      SPARK_Pkg_Id : Entity_Id;
      Heap_Pkg_Id  : Entity_Id;
      --  Entities for the packages that enclose the created state

      State_Name_Id : Name_Id;
      --  Name of the create state

      Decl : Node_Id;
      --  A fake declaration for the created state; it will be examined by
      --  Einfo.Has_Option when it queries the state properties.

   begin
      pragma Assert (No (Dynamic_Memory_Id));

      --  Create and decorate entities for the abstract state and its enclosing
      --  packages, so that we can use typical queries and, in particular,
      --  get its Unique_Name (which is rather fragile, as it involves a child
      --  unit).

      --  Create SPARK package

      SPARK_Pkg_Id :=
        Make_Defining_Identifier
          (No_Location, Name_SPARK);

      Set_Ekind (SPARK_Pkg_Id, E_Package);
      Set_Scope (SPARK_Pkg_Id, Standard_Standard);

      --  Create SPARK.Heap package

      Heap_Pkg_Id :=
        Make_Defining_Identifier
          (No_Location, Name_Find (Heap_Pkg_Name));

      Set_Ekind (Heap_Pkg_Id, E_Package);
      Set_Scope (Heap_Pkg_Id, SPARK_Pkg_Id);
      Set_Is_Child_Unit (Heap_Pkg_Id);

      --  Create SPARK.Heap.Dynamic_Memory abstract state

      State_Name_Id := Name_Find (Dynamic_Memory_Name);

      Dynamic_Memory_Id :=
        Make_Defining_Identifier
          (No_Location, State_Name_Id);

      Set_Ekind (Dynamic_Memory_Id, E_Abstract_State);
      Set_Etype (Dynamic_Memory_Id, Standard_Void_Type);
      Set_Scope (Dynamic_Memory_Id, Heap_Pkg_Id);

      --  Create a fake declaration of the form:
      --     "[State_Name_Id] with External => Async_Writers"
      --
      --  and attach it to the state's entity to make those
      --  properties recognized by queries like Is_External_State
      --  and Async_Writers_Enabled.

      Decl :=
        Make_Extension_Aggregate
          (Sloc          => No_Location,
           Ancestor_Part =>
             Make_Identifier
               (Sloc  => No_Location,
                Chars => State_Name_Id),
           Component_Associations =>
             New_List
               (Make_Component_Association
                  (Sloc       => No_Location,
                   Choices    =>
                     New_List
                       (Make_Identifier
                          (Sloc  => No_Location,
                           Chars => Name_External)),
                   Expression =>
                     Make_Identifier
                       (Sloc  => No_Location,
                        Chars => Name_Async_Writers))));

      Set_Parent (Dynamic_Memory_Id, Decl);

      --  ??? perhaps we should set Is_Internal as well
   end Create_Heap_State;

   ----------------
   -- Heap_State --
   ----------------

   function Heap_State return Entity_Id is (Dynamic_Memory_Id);

   -------------------
   -- Is_Heap_State --
   -------------------

   function Is_Heap_State (E : Entity_Id) return Boolean is
   begin
      pragma Assert (Present (Dynamic_Memory_Id));

      return E = Dynamic_Memory_Id;
   end Is_Heap_State;

end Flow.Dynamic_Memory;
