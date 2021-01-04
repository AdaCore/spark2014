------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                   F L O W . D Y N A M I C _ M E M O R Y                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2019-2021, Altran UK Limited                --
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

with Elists;      use Elists;
with Lib;         use Lib;
with Namet;       use Namet;
with Nlists;      use Nlists;
with Nmake;       use Nmake;
with Sem_Util;    use Sem_Util;
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

   procedure Find_Heap_State (E : Entity_Id);
   --  Finds an abstract state that represents memory (de)allocation in
   --  compilation unit whose main entity is E.

   procedure Scan_All_Units;
   --  Scans all compilation units analyzed by the frontend, i.e. the current
   --  compilation unit and all units transitively WITH-ed from it (except for
   --  Standard) and check if they contain the abstract state that represents
   --  memory (de)allocation.

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
      Scan_All_Units;

      if Present (Dynamic_Memory_Id) then
         return;
      end if;

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

   ---------------------
   -- Find_Heap_State --
   ---------------------

   procedure Find_Heap_State (E : Entity_Id) is
      State_Id : Entity_Id;
   begin
      --  Check as strictly as possible, first the enclosing package...

      if Ekind (E) = E_Package
        and then Get_Name_String (Chars (E)) = Heap_Pkg_Name
        and then Ekind (Scope (E)) = E_Package
        and then Chars (Scope (E)) = Name_SPARK
        and then Scope (Scope (E)) = Standard_Standard
        and then Has_Non_Null_Abstract_State (E)
        and then List_Length (Abstract_States (E)) = 1

      --  ... then the abstract state itself

      then
         State_Id :=
           Node (First_Elmt (Abstract_States (E)));

         if Get_Name_String (Chars (State_Id)) = Dynamic_Memory_Name
           and then Is_External_State (State_Id)
           and then not Async_Readers_Enabled (State_Id)
           and then Async_Writers_Enabled (State_Id)
           and then not Effective_Reads_Enabled (State_Id)
           and then not Effective_Writes_Enabled (State_Id)
         then
            Dynamic_Memory_Id := State_Id;
         end if;
      end if;
   end Find_Heap_State;

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

   --------------------
   -- Scan_All_Units --
   --------------------

   procedure Scan_All_Units is
   begin
      --  The following is like Gnat2Why.Driver.Process_All_Units, except for:
      --  1) ignoring Standard
      --  2) looking at the CUnit_Entity and not the node of a compilation unit
      --  3) exiting early if we find what we are searching for.

      --  Iterate over all other units known to the frontend
      for U in Main_Unit .. Last_Unit loop

         --  Ignore non-compilation units (e.g. .adc configuration files)
         --  and units that were not analysed (e.g. system.ads when it is
         --  implicitly pulled by Ensure_System_Dependency).

         if Present (Cunit (U))
           and then Analyzed (Unit (Cunit (U)))
         then
            Find_Heap_State (Cunit_Entity (U));
         end if;

         exit when Present (Dynamic_Memory_Id);
      end loop;
   end Scan_All_Units;

end Flow.Dynamic_Memory;
