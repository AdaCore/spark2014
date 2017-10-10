------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                S P A R K _ F R A M E _ C O N D I T I O N S               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2011-2017, AdaCore                     --
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
with Sem_Aux;                        use Sem_Aux;
with Snames;                         use Snames;
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

   Propagate_Error_For_Missing_Scope : Boolean := True;
   --  By default, propagate an error if a scope is missing, unless set to
   --  False for a degraded mode of operation in which such errors are ignored.

   Scopes       : Name_Sets.Set;    --  All scope entities

   Defines      : Name_Graphs.Map;  --  Entities defined by each scope
   Writes       : Name_Graphs.Map;  --  Entities written in each scope
   Reads        : Name_Graphs.Map;  --  Entities read in each scope
   Callers      : Name_Graphs.Map;  --  Callers for each subprogram
   Calls        : Name_Graphs.Map;  --  Subprograms called in each subprogram

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Add_To_Map (Map : in out Name_Graphs.Map; From, To : Entity_Name);
   --  Add the relation From -> To in map Map

   function Make_Entity_Name (Name : String_Ptr) return Entity_Name
   with Pre => Name /= null and then Name.all /= "";
   --  Build a name for an entity, making sure the name is not empty

   procedure Set_Default_To_Empty
     (Map  : in out Name_Graphs.Map;
      Name : Entity_Name)
   with Post => Map.Contains (Name);
   --  Make sure that element Name has an entry in Map. If not already present,
   --  add one which maps the element to the empty set.

   ----------------
   -- Add_To_Map --
   ----------------

   procedure Add_To_Map (Map : in out Name_Graphs.Map; From, To : Entity_Name)
   is
      Ignored  : Boolean;
      Position : Name_Graphs.Cursor;

   begin
      --  Try to insert a default value (i.e. empty set) and then update it
      Map.Insert (Key      => From,
                  Position => Position,
                  Inserted => Ignored);
      Map (Position).Include (To);
   end Add_To_Map;

   ------------------
   -- Display_Maps --
   ------------------

   procedure Display_Maps is

      use Name_Graphs;

      procedure Display_Entity (E : Entity_Name);
      procedure Display_One_Map (Map : Name_Graphs.Map; Name, Action : String);
      procedure Display_One_Set (Set : Name_Sets.Set);

      --------------------
      -- Display_Entity --
      --------------------

      procedure Display_Entity (E : Entity_Name) is
      begin
         Put ("entity " & To_String (E));
      end Display_Entity;

      ---------------------
      -- Display_One_Map --
      ---------------------

      procedure Display_One_Map (Map : Name_Graphs.Map; Name, Action : String)
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

      procedure Display_One_Set (Set : Name_Sets.Set) is
      begin
         for Ent of Set loop
            Put ("  "); Display_Entity (Ent); New_Line;
         end loop;
      end Display_One_Set;

   --  Start of processing for Display_Maps

   begin
      Display_One_Map (Defines, "Variables defined by subprograms", "defines");
      New_Line;
      Display_One_Map (Reads, "Variables read by subprograms", "reads");
      New_Line;
      Display_One_Map (Writes, "Variables written by subprograms", "writes");
      New_Line;
      Display_One_Map (Calls, "Subprograms called", "calls");
      New_Line;
      Display_One_Map (Callers, "Callers of subprograms", "is called by");
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
              else Empty);
   end Find_Entity;

   --------------------
   -- Computed_Calls --
   --------------------

   function Computed_Calls (E_Name : Entity_Name) return Name_Sets.Set
     renames Calls.Element;

   --------------------
   -- Computed_Reads --
   --------------------

   function Computed_Reads (E : Entity_Id) return Name_Sets.Set
   is
      pragma Assert (if Ekind (E) = E_Entry then No (Alias (E)));
      --  Alias is empty for entries and meaningless for entry families

      E_Alias : constant Entity_Id :=
        (if Ekind (E) in E_Function | E_Procedure
           and then Present (Alias (E))
         then Ultimate_Alias (E)
         else E);

      E_Name   : constant Entity_Name := To_Entity_Name (E_Alias);
      Read_Ids : Name_Sets.Set := Name_Sets.Empty_Set;

      use type Name_Sets.Set;

   begin
      --  ??? Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, instead return empty sets.

      if Is_Subprogram_Or_Entry (E)
        and then Ekind (E) /= E_Entry_Family
        and then Is_Abstract_Subprogram (E_Alias)
      then
         return Name_Sets.Empty_Set;
      end if;

      Read_Ids := Reads (E_Name);

      return Read_Ids - Defines (E_Name);
   exception
      when Constraint_Error =>
         if Propagate_Error_For_Missing_Scope then
            raise Constraint_Error with
              ("missing effects for subprogram " & To_String (E_Name));
         else
            return Name_Sets.Empty_Set;
         end if;
   end Computed_Reads;

   ---------------------
   -- Computed_Writes --
   ---------------------

   function Computed_Writes (E : Entity_Id) return Name_Sets.Set is
      pragma Assert (if Ekind (E) = E_Entry then No (Alias (E)));
      --  Alias is empty for entries and meaningless for entry families

      E_Alias : constant Entity_Id :=
        (if Ekind (E) in E_Function | E_Procedure
           and then Present (Alias (E))
         then Ultimate_Alias (E)
         else E);

      E_Name    : constant Entity_Name := To_Entity_Name (E_Alias);
      Write_Ids : Name_Sets.Set := Name_Sets.Empty_Set;

      use type Name_Sets.Set;

   begin
      --  ??? Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, which do not have effects, instead return the empty set.

      if Is_Subprogram_Or_Entry (E)
        and then Ekind (E) /= E_Entry_Family
        and then Is_Abstract_Subprogram (E_Alias)
      then
         return Name_Sets.Empty_Set;
      end if;

      --  Go through the reads and check if the entities corresponding to
      --  variables (not constants) have pragma Effective_Reads set. If so,
      --  then these entities are also writes.
      --  ??? call to Computed_Reads repeats what is already done here; this
      --  should be refactored.
      for E_N of Computed_Reads (E) loop
         declare
            Read : constant Entity_Id := Find_Entity (E_N);
         begin
            --  ??? how about entities represented by entity names?
            if Present (Read)
              and then Ekind (Read) = E_Variable
              and then Present (Get_Pragma (Read, Pragma_Effective_Reads))
            then
               Write_Ids.Insert (E_N);
            end if;
         end;
      end loop;

      Write_Ids.Union (Writes (E_Name));

      return Write_Ids - Defines (E_Name);
   exception
      when Constraint_Error =>
         if Propagate_Error_For_Missing_Scope then
            raise Constraint_Error with
              ("missing effects for subprogram " & To_String (E_Name));
         else
            return Name_Sets.Empty_Set;
         end if;
   end Computed_Writes;

   ----------------------
   -- Is_Heap_Variable --
   ----------------------

   function Is_Heap_Variable (Ent : Entity_Name) return Boolean is
     (To_String (Ent) = SPARK_Xrefs.Name_Of_Heap_Variable);

   ----------------------
   -- Load_SPARK_Xrefs --
   ----------------------

   procedure Load_SPARK_Xrefs is

      type Scope_Name is record
         File_Num  : Pos;
         Scope_Num : Pos;
      end record;
      --  Name representative of a scope

      function Scope_Hash (S : Scope_Name) return Hash_Type is
        (Hash_Type (S.File_Num * 17 + S.Scope_Num));
      --  Hash function for hashed-maps

      package Scope_Entity is new Hashed_Maps
        (Key_Type        => Scope_Name,
         Element_Type    => Entity_Name,
         Hash            => Scope_Hash,
         Equivalent_Keys => "=");
      --  Map each scope to its entity representative

      package Scope_Spec is new Hashed_Maps
        (Key_Type        => Scope_Name,
         Element_Type    => Scope_Name,
         Hash            => Scope_Hash,
         Equivalent_Keys => "=");
      --  Map body scopes to their spec scope, when different

      Scope_Entities : Scope_Entity.Map;
      Scope_Specs    : Scope_Spec.Map;
      Current_Entity : Any_Entity_Name;

      function Scope_Name_To_Scope_Entity
        (N : Scope_Name) return Entity_Name;
      --  Convert low-level numeric representation to symbol

      ---------------------------------
      --  Scope_Name_To_Scope_Entity --
      ---------------------------------

      function Scope_Name_To_Scope_Entity
        (N : Scope_Name) return Entity_Name
      is
         C : constant Scope_Spec.Cursor := Scope_Specs.Find (N);
      begin
         return
           Scope_Entities
             (if Scope_Spec.Has_Element (C)
              then Scope_Specs (C)
              else N);
      end Scope_Name_To_Scope_Entity;

   --  Start of processing for Load_SPARK_Xrefs

   begin
      --  Fill Scope_Entities : build entity representatives for all scopes in
      --  this ALI file.

      --  Fill Scope_Specs : build a correspondence table between body and spec
      --  scope for the same entity.

      for F in SPARK_File_Table.First .. SPARK_File_Table.Last loop
         for S in SPARK_File_Table.Table (F).From_Scope
           .. SPARK_File_Table.Table (F).To_Scope
         loop
            declare
               Srec : SPARK_Scope_Record renames
                 SPARK_Scope_Table.Table (S);
               Sco  : constant Scope_Name :=
                 Scope_Name'(File_Num  => Srec.File_Num,
                             Scope_Num => Srec.Scope_Num);
               Ent  : constant Entity_Name :=
                 Make_Entity_Name (Srec.Scope_Name);
            begin
               Scope_Entities.Insert (Sco, Ent);

               --  Record which entities are scopes, for default initializing
               --  maps in Propagate_Through_Call_Graph.

               Scopes.Include (Ent);

               --  If present, use the body-to-spec information

               if Srec.Spec_File_Num /= 0 then
                  Scope_Specs.Insert
                    (Sco,
                     Scope_Name'(File_Num  => Srec.Spec_File_Num,
                                 Scope_Num => Srec.Spec_Scope_Num));
               end if;
            end;
         end loop;
      end loop;

      --  Fill in high-level tables from xrefs

      Current_Entity := Null_Entity_Name;
      for F in SPARK_File_Table.First .. SPARK_File_Table.Last
      loop
         for S in SPARK_File_Table.Table (F).From_Scope ..
           SPARK_File_Table.Table (F).To_Scope
         loop
            declare
               Srec : SPARK_Scope_Record renames
                 SPARK_Scope_Table.Table (S);

               Def_Scope_Ent : constant Entity_Name :=
                 Scope_Name_To_Scope_Entity
                   (Scope_Name'(File_Num  => Srec.File_Num,
                                Scope_Num => Srec.Scope_Num));
               --  Scope of the definition

            begin
               for X in SPARK_Scope_Table.Table (S).From_Xref ..
                 SPARK_Scope_Table.Table (S).To_Xref
               loop
                  Do_One_Xref : declare

                     Xref : SPARK_Xref_Record renames
                       SPARK_Xref_Table.Table (X);

                     Ref_Entity : constant Entity_Name :=
                       Make_Entity_Name (Xref.Entity_Name);

                     Ref_Scope_Ent : constant Entity_Name :=
                       Scope_Name_To_Scope_Entity
                         (Scope_Name'(File_Num  => Xref.File_Num,
                                      Scope_Num => Xref.Scope_Num));
                     --  Scope being referenced

                  begin
                     --  Register the definition on first occurence of
                     --  variables.

                     if Current_Entity /= Ref_Entity
                       and then not Is_Heap_Variable (Ref_Entity)
                       and then Xref.Rtype in 'c' | 'r' | 'm'
                     then
                        Add_To_Map (Defines,
                                    Def_Scope_Ent,
                                    Ref_Entity);
                     end if;

                     --  Register xref according to type

                     case Xref.Rtype is
                        when 'r' =>
                           Add_To_Map (Reads, Ref_Scope_Ent, Ref_Entity);
                        when 'c' =>
                           Add_To_Map (Reads, Ref_Scope_Ent, Ref_Entity);
                        when 'm' =>
                           Add_To_Map (Writes, Ref_Scope_Ent, Ref_Entity);
                        when 's' =>
                           Add_To_Map (Calls, Ref_Scope_Ent, Ref_Entity);
                           Add_To_Map (Callers, Ref_Entity, Ref_Scope_Ent);
                        when others =>
                           raise Program_Error;
                     end case;

                     Current_Entity := Ref_Entity;
                  end Do_One_Xref;
               end loop;
            end;
         end loop;
      end loop;
   end Load_SPARK_Xrefs;

   ----------------------
   -- Make_Entity_Name --
   ----------------------

   function Make_Entity_Name (Name : String_Ptr) return Entity_Name is
     (To_Entity_Name (Name.all));

   ----------------------------------
   -- Propagate_Through_Call_Graph --
   ----------------------------------

   procedure Propagate_Through_Call_Graph
   is
      use Name_Graphs;

   begin
      --  Set error propagation mode for missing scopes

      Propagate_Error_For_Missing_Scope := False;

      --  Declare missing scopes, which occurs for generic instantiations (see
      --  K523-007) until a proper treatment of generics. We take into account
      --  all subprograms called.

      for C in Callers.Iterate loop
         Scopes.Include (Key (C));
      end loop;

      --  Initialize all maps so that each subprogram has an entry in each map.
      --  This is not needed for File_Defines.

      for Scope of Scopes loop
         Set_Default_To_Empty (Defines, Scope);
         Set_Default_To_Empty (Writes,  Scope);
         Set_Default_To_Empty (Reads,   Scope);
         Set_Default_To_Empty (Callers, Scope);
         Set_Default_To_Empty (Calls,   Scope);
      end loop;
   end Propagate_Through_Call_Graph;

   ---------------------
   -- Register_Entity --
   ---------------------

   procedure Register_Entity (E : Entity_Id) is
      E_Name : constant Entity_Name := To_Entity_Name (E);
   begin
      Name_To_Entity.Include (E_Name, E);
   end Register_Entity;

   --------------------------
   -- Set_Default_To_Empty --
   --------------------------

   procedure Set_Default_To_Empty
     (Map  : in out Name_Graphs.Map;
      Name : Entity_Name)
   is
      Inserted : Boolean;
      Position : Name_Graphs.Cursor;
      --  Dummy variables required by the container API

   begin
      Map.Insert (Key      => Name,
                  Position => Position,
                  Inserted => Inserted);
      --  Attempt to map entity Ent to a default element (i.e. empty set)
   end Set_Default_To_Empty;

   -------------------------------------
   -- Collect_Direct_Computed_Globals --
   -------------------------------------

   procedure Collect_Direct_Computed_Globals
     (E       :     Entity_Id;
      Inputs  : out Name_Sets.Set;
      Outputs : out Name_Sets.Set)
   is
      pragma Assert (if Ekind (E) = E_Entry then No (Alias (E)));
      --  Alias is empty for entries and meaningless for entry families

      E_Alias : constant Entity_Id :=
        (if Ekind (E) in E_Function | E_Procedure
           and then Present (Alias (E))
         then Ultimate_Alias (E)
         else E);

   begin
      --  ??? Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, instead return empty sets.

      if Is_Subprogram_Or_Entry (E)
        and then Ekind (E) /= E_Entry_Family
        and then Is_Abstract_Subprogram (E_Alias)
      then
         --  Initialize to empty sets and return
         Inputs  := Name_Sets.Empty_Set;
         Outputs := Name_Sets.Empty_Set;

         return;
      end if;

      Inputs  := Computed_Reads (E);
      Outputs := Computed_Writes (E);

      --  Add variables written to variables read
      --  ??? for composite variables fine, but why for simple ones?
      Inputs.Union (Outputs);
   end Collect_Direct_Computed_Globals;

end SPARK_Frame_Conditions;
