------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                S P A R K _ F R A M E _ C O N D I T I O N S               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2011-2021, AdaCore                     --
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

with Ada.Containers;                 use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Text_IO;                    use Ada.Text_IO;
with Lib.Xref;                       use Lib.Xref;
with Sem_Aux;                        use Sem_Aux;
with Sem_Util;                       use Sem_Util;
with Snames;                         use Snames;
with SPARK_Util;                     use SPARK_Util;
with SPARK_Xrefs;                    use SPARK_Xrefs;

package body SPARK_Frame_Conditions is

   -----------------
   -- Local Types --
   -----------------

   package Name_To_Entity_Map is new Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Entity_Id,
      Hash            => Name_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Name_To_Entity : Name_To_Entity_Map.Map := Name_To_Entity_Map.Empty_Map;

   ---------------------
   -- Local Variables --
   ---------------------

   Writes : Node_Graphs.Map;  --  Entities written in each scope
   Reads  : Node_Graphs.Map;  --  Entities read in each scope
   Calls  : Node_Graphs.Map;  --  Subprograms called in each subprogram

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Add_To_Map (Map : in out Node_Graphs.Map; From, To : Entity_Id);
   --  Add the relation From -> To in map Map

   function Get_Frontend_Xrefs
     (Map : Node_Graphs.Map;
      Key : Entity_Id)
      return Node_Sets.Set;
   --  Returns nodes stored in Map for Key or an empty set if Key is not in Map

   ----------------
   -- Add_To_Map --
   ----------------

   procedure Add_To_Map (Map : in out Node_Graphs.Map; From, To : Entity_Id) is
   begin
      if not Is_Generic_Unit (From) then
         declare
            Inserted : Boolean;
            Position : Node_Graphs.Cursor;

         begin
            Map.Insert (Key      => From,
                        Position => Position,
                        Inserted => Inserted);

            Map (Position).Include (To);
         end;
      end if;
   end Add_To_Map;

   ------------------
   -- Display_Maps --
   ------------------

   procedure Display_Maps is

      use Node_Graphs;

      procedure Display_Entity (E : Entity_Id);
      procedure Display_One_Map (Map : Node_Graphs.Map; Name, Action : String);
      procedure Display_One_Set (Set : Node_Sets.Set);

      --------------------
      -- Display_Entity --
      --------------------

      procedure Display_Entity (E : Entity_Id) is
      begin
         Put ("entity " & Unique_Name (E));
      end Display_Entity;

      ---------------------
      -- Display_One_Map --
      ---------------------

      procedure Display_One_Map (Map : Node_Graphs.Map; Name, Action : String)
      is
      begin
         Put_Line ("-- " & Name & " --");

         for Cu in Map.Iterate loop
            Display_Entity (Key (Cu));
            Put_Line (" " & Action);
            Display_One_Set (Map (Cu));
         end loop;
      end Display_One_Map;

      ---------------------
      -- Display_One_Set --
      ---------------------

      procedure Display_One_Set (Set : Node_Sets.Set) is
      begin
         for Ent of Set loop
            Put ("  "); Display_Entity (Ent); New_Line;
         end loop;
      end Display_One_Set;

   --  Start of processing for Display_Maps

   begin
      Display_One_Map (Reads, "Variables read by subprograms", "reads");
      New_Line;
      Display_One_Map (Writes, "Variables written by subprograms", "writes");
      New_Line;
      Display_One_Map (Calls, "Subprograms called", "calls");
   end Display_Maps;

   -----------------
   -- Find_Entity --
   -----------------

   function Find_Entity (E : Entity_Name) return Entity_Id is
      use Name_To_Entity_Map;
      C : constant Name_To_Entity_Map.Cursor := Name_To_Entity.Find (E);

   begin
      return (if Has_Element (C)
              then Element (C)
              else Types.Empty);
   end Find_Entity;

   ------------------------
   -- Get_Frontend_Xrefs --
   ------------------------

   function Get_Frontend_Xrefs
     (Map : Node_Graphs.Map;
      Key : Entity_Id)
      return Node_Sets.Set
   is
      C : constant Node_Graphs.Cursor := Map.Find (Key);

   begin
      return
        (if Node_Graphs.Has_Element (C)
         then Map (C)
         else Node_Sets.Empty_Set);
   end Get_Frontend_Xrefs;

   --------------------
   -- Computed_Calls --
   --------------------

   function Computed_Calls (E : Entity_Id) return Node_Sets.Set is
     (Get_Frontend_Xrefs (Calls, E));

   ----------------------
   -- Is_Heap_Variable --
   ----------------------

   function Is_Heap_Variable (Ent : Entity_Name) return Boolean is
     (To_String (Ent) = SPARK_Xrefs.Name_Of_Heap_Variable);

   function Is_Heap_Variable (E : Entity_Id) return Boolean is
     (E = SPARK_Xrefs.Heap);

   ----------------------
   -- Load_SPARK_Xrefs --
   ----------------------

   procedure Load_SPARK_Xrefs is

      function Ignore_Object_Reference
        (E       : Entity_Id;
         Context : Entity_Id)
         return Boolean;
      --  Returns True if reference to E from within Context should be ignored;
      --  this happens either when E is declared within the Context itself (so
      --  does not contribute to the Global contract) or when it is a
      --  quantified loop variable (that also does contribute to the Global
      --  contract) that is likely to badly handled if it appear inside
      --  expression functions.

      procedure Load_SPARK_Xref (Index : Int; Xref : SPARK_Xref_Record);
      --  Load a single frontend reference into backend data structures

      procedure Load is new
        SPARK_Specific.Iterate_SPARK_Xrefs (Load_SPARK_Xref);
      --  Load all frontend cross-references

      -----------------------------
      -- Ignore_Object_Reference --
      -----------------------------

      function Ignore_Object_Reference
        (E       : Entity_Id;
         Context : Entity_Id)
         return Boolean
      is
      begin
         return Scope_Within (E, Context)
           or else (Ekind (E) in E_Loop_Parameter | E_Variable
                    and then Is_Quantified_Loop_Param (E));
      end Ignore_Object_Reference;

      ---------------------
      -- Load_SPARK_Xref --
      ---------------------

      procedure Load_SPARK_Xref (Index : Int; Xref : SPARK_Xref_Record) is
         pragma Unreferenced (Index);

         Ref_Entity : constant Entity_Id := Unique_Entity (Xref.Entity);
         Ref_Scope  : constant Entity_Id := Unique_Entity (Xref.Ref_Scope);
         --  Referenced entity and scope where the reference occurs

      begin
         --  Register xref according to type

         case Xref.Rtype is
            when 'r' =>
               if not Ignore_Object_Reference (Ref_Entity, Ref_Scope) then
                  Add_To_Map (Reads,  Ref_Scope, Ref_Entity);
               end if;
            when 'm' =>
               if not Ignore_Object_Reference (Ref_Entity, Ref_Scope) then
                  Add_To_Map (Writes, Ref_Scope, Ref_Entity);
               end if;
            when 's' =>
               if not In_Generic_Scope (Ref_Entity) then
                  Add_To_Map (Calls,  Ref_Scope, Ref_Entity);
               end if;
            when others =>
               raise Program_Error;
         end case;
      end Load_SPARK_Xref;

   --  Start of processing for Load_SPARK_Xrefs

   begin
      Load;
   end Load_SPARK_Xrefs;

   ---------------------
   -- Register_Entity --
   ---------------------

   procedure Register_Entity (E : Entity_Id) is
      E_Name : constant Entity_Name := To_Entity_Name (E);
   begin
      Name_To_Entity.Include (E_Name, E);
   end Register_Entity;

   -------------------------------------
   -- Collect_Direct_Computed_Globals --
   -------------------------------------

   procedure Collect_Direct_Computed_Globals
     (E       :     Entity_Id;
      Inputs  : out Node_Sets.Set;
      Outputs : out Node_Sets.Set)
   is
      pragma Assert
        (if Is_Subprogram (E) then
           E = Ultimate_Alias (E)
         elsif Ekind (E) = E_Entry then
           No (Alias (E)));
      --  We should only deal with ultimate subprogram aliases here; for
      --  entries alias is always empty, while for entry families and tasks it
      --  is meaningless.

   begin
      --  ??? Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, instead return empty sets.

      if Is_Subprogram (E)
        and then Is_Abstract_Subprogram (E)
      then
         --  Initialize to empty sets and return
         Inputs  := Node_Sets.Empty_Set;
         Outputs := Node_Sets.Empty_Set;

         return;
      end if;

      Inputs  := Get_Frontend_Xrefs (Reads,  E);
      Outputs := Get_Frontend_Xrefs (Writes, E);

      --  Go through the reads and check if the entities corresponding to
      --  variables (not constants) have pragma Effective_Reads set. If so,
      --  then these entities are also writes.
      for Input of Inputs loop
         if Ekind (Input) = E_Variable
           and then Present (Get_Pragma (Input, Pragma_Effective_Reads))
         then
            Outputs.Include (Input);
         end if;
      end loop;

      --  Add variables written to variables read
      --  ??? for composite variables fine, but why for simple ones?
      Inputs.Union (Outputs);
   end Collect_Direct_Computed_Globals;

end SPARK_Frame_Conditions;
