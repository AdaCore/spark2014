------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                S P A R K _ F R A M E _ C O N D I T I O N S               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2011-2016, AdaCore                     --
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

with Ada.Containers.Hashed_Maps;
with Ada.Containers.Vectors;
with Ada.Text_IO;                    use Ada.Text_IO;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Types;                     use Flow_Types;
with Flow_Utility;                   use Flow_Utility;
with Get_SPARK_Xrefs;
with Lib.Xref;                       use Lib.Xref;
with Sem_Aux;                        use Sem_Aux;
with Snames;                         use Snames;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;
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

   package Entity_Name_Vectors is new
     Ada.Containers.Vectors (Index_Type   => Positive,
                             Element_Type => Entity_Name);

   subtype SCC is Entity_Name_Vectors.Vector;
   --  Ordered list of subprograms in a strongly connected component, roughly
   --  ordered so as to follow call chains for better propagation.

   package SCC_Vectors is new
     Ada.Containers.Vectors (Index_Type   => Positive,
                             Element_Type => SCC,
                             "="          => Entity_Name_Vectors."=");

   subtype SCCs is SCC_Vectors.Vector;
   --  Ordered list of strongly connected components in call-graph, with the
   --  "leaf" SCCs coming first.
   --
   --  ??? originally this code was using arrays, which was difficult to follow
   --  and required manual memory allocation and freeing; now it uses vectors,
   --  which makes it easier to understand; perhaps with lists it would be even
   --  cleaner, but I suspect that vectors give slightly better performance
   --  because of data locality. Lastly, the transitive closure algorithm
   --  that is used in flow analysis should give even better performance.

   ---------------------
   -- Local Variables --
   ---------------------

   Propagate_Error_For_Missing_Scope : Boolean := True;
   --  By default, propagate an error if a scope is missing, unless set to
   --  False for a degraded mode of operation in which such errors are ignored.

   Scopes       : Name_Sets.Set;    --  All scope entities
   Constants    : Name_Sets.Set;    --  All constants

   File_Defines : Name_Maps.Map;    --  File defining each entities
   Defines      : Name_Graphs.Map;  --  Entities defined by each scope
   Writes       : Name_Graphs.Map;  --  Entities written in each scope
   Reads        : Name_Graphs.Map;  --  Entities read in each scope
   Callers      : Name_Graphs.Map;  --  Callers for each subprogram
   Calls        : Name_Graphs.Map;  --  Subprograms called in each subprogram

   Protected_Operations : Name_Sets.Set;
   --  All protected operations, i.e. entries, protected functions and
   --  protected procedures.

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Add_To_Map (Map : in out Name_Graphs.Map; From, To : Entity_Name);
   --  Add the relation From -> To in map Map

   function Compute_Strongly_Connected_Components
     (Nodes : Name_Sets.Set) return SCCs;
   --  Compute of strongly connected components using Tarjan's algorithm.
   --  Individual components are dynamically allocated.

   function Count_In_Map
     (Map : Name_Graphs.Map;
      Ent : Entity_Name) return Count_Type;
   --  Return the number of elements in the set associated to Ent in Map, or
   --  else 0.

   function Make_Entity_Name (Name : String_Ptr) return Entity_Name
   with Pre => Name /= null and then Name.all /= "";
   --  Build a name for an entity, making sure the name is not empty

   procedure Set_Default_To_Empty
     (Map : in out Name_Graphs.Map;
      Set : Name_Sets.Set);
   --  Make sure each element in Set has an entry in Map. If not already
   --  present, add one which maps the element to the empty set.

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

   -------------------------------------------
   -- Compute_Strongly_Connected_Components --
   -------------------------------------------

   function Compute_Strongly_Connected_Components
     (Nodes : Name_Sets.Set) return SCCs
   is
      Cur_SCCs : SCCs;

      package Value_Map is new Hashed_Maps
        (Key_Type        => Entity_Name,
         Element_Type    => Positive,
         Hash            => Name_Hash,
         Equivalent_Keys => "=",
         "="             => "=");
      --  Map used internally in strongly connected component computation. Not
      --  to be confused with map over ids.

      Indexes  : Value_Map.Map;
      Lowlinks : Value_Map.Map;

      Index : Positive := 1;

      -----------------------
      -- Local Subprograms --
      -----------------------

      procedure Strong_Connect (V : Entity_Name);
      --  Compute SCC for V, possibly generating other reachable SCCs before
      --  returning.

      --------------------
      -- Stack of nodes --
      --------------------

      type Stack is record
         Data    : Entity_Name_Vectors.Vector;
         Content : Name_Sets.Set;
      end record;

      S : Stack;

      procedure Push (E : Entity_Name);
      function Pop return Entity_Name;
      function Has (E : Entity_Name) return Boolean;

      ----------
      -- Push --
      ----------

      procedure Push (E : Entity_Name) is
      begin
         S.Content.Insert (E);
         S.Data.Append (E);
      end Push;

      ---------
      -- Pop --
      ---------

      function Pop return Entity_Name is
         E : constant Entity_Name := S.Data.Last_Element;
      begin
         S.Content.Delete (E);
         S.Data.Delete_Last;
         return E;
      end Pop;

      ---------
      -- Has --
      ---------

      function Has (E : Entity_Name) return Boolean
        renames S.Content.Contains;

      --------------------
      -- Strong_Connect --
      --------------------

      procedure Strong_Connect (V : Entity_Name) is
      begin
         --  Set the depth index for V to the smallest unused index

         Indexes.Include (V, Index);
         Lowlinks.Include (V, Index);
         Index := Index + 1;
         Push (V);

         --  Consider successors of V

         for W of Calls (V) loop
            --  Ignore leaf nodes in call-graph as no treatment is needed
            --  for them.

            if not Nodes.Contains (W) then
               null;

            --  Successor W has not yet been visited; recurse on it

            elsif not Indexes.Contains (W) then
               Strong_Connect (W);
               Lowlinks.Include
                 (V, Natural'Min
                    (Lowlinks.Element (V), Lowlinks.Element (W)));

            --  Successor W is in stack S and hence in the current SCC

            elsif Has (W) then
               Lowlinks.Include
                 (V, Natural'Min
                    (Lowlinks.Element (V), Indexes.Element (W)));
            end if;

         end loop;

         --  If V is a root node, pop the stack and generate an SCC

         if Lowlinks (V) = Indexes (V) then
            declare
               Size_Of_Current_SCC : constant Positive :=
                 S.Data.Last_Index - S.Data.Reverse_Find_Index (V) + 1;
               --  Size of the current SCC sitting on the stack

               Cur_SCC : SCC;
               --  A new strongly connected component

            begin
               Cur_SCC.Reserve_Capacity (Count_Type (Size_Of_Current_SCC));

               for J in 1 .. Size_Of_Current_SCC loop
                  Cur_SCC.Append (Pop);
               end loop;

               pragma Assert (Cur_SCC.Last_Element = V);

               --  Output the current strongly connected component

               Cur_SCCs.Append (Entity_Name_Vectors.Empty_Vector);
               Entity_Name_Vectors.Move (Target => Cur_SCCs (Cur_SCCs.Last),
                                         Source => Cur_SCC);
            end;
         end if;
      end Strong_Connect;

   --  Start of processing for Compute_Strongly_Connected_Components

   begin
      --  There are at most as many SCCs as nodes (if no recursion at all)
      Cur_SCCs.Reserve_Capacity (Nodes.Length);

      for V of Nodes loop
         if not Indexes.Contains (V) then
            Strong_Connect (V);
         end if;
      end loop;

      return Cur_SCCs;
   end Compute_Strongly_Connected_Components;

   ------------------
   -- Count_In_Map --
   ------------------

   function Count_In_Map
     (Map : Name_Graphs.Map;
      Ent : Entity_Name) return Count_Type
   is
      C : constant Name_Graphs.Cursor := Map.Find (Ent);
   begin
      return (if Name_Graphs.Has_Element (C)
              then Map (C).Length
              else 0);
   end Count_In_Map;

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

   --------------------
   -- File_Of_Entity --
   --------------------

   function File_Of_Entity (E : Entity_Name) return Entity_Name
     renames File_Defines.Element;

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

   ------------------------------
   -- For_All_External_Objects --
   ------------------------------

   procedure For_All_External_Objects
     (Process : not null access procedure (E : Entity_Name))
   is
   begin
      for S of Defines loop
         --  External objects are those in the sets of defined objects Defines,
         --  that are not constant objects from the set Constants.

         for Elt of S loop
            if not Constants.Contains (Elt)
              and then not Translated_Object_Entities.Contains (Elt)
            then
               Process (Elt);
            end if;
         end loop;
      end loop;
   end For_All_External_Objects;

   -----------------------------
   -- For_All_External_States --
   -----------------------------

   procedure For_All_External_States
     (Process : not null access procedure (E : Entity_Name))
   is
   begin
      for State_Name of GG_Get_State_Abstractions loop
         --  Any state abstraction for which we do NOT have a
         --  corresponding Entidy_Id is an External state abstraction.

         if No (Find_Entity (State_Name)) then
            Process (State_Name);
         end if;
      end loop;
   end For_All_External_States;

   --------------------
   -- Computed_Calls --
   --------------------

   function Computed_Calls (E : Entity_Name) return Name_Sets.Set
     renames Calls.Element;

   --------------------
   -- Computed_Reads --
   --------------------

   function Computed_Reads
     (E                 : Entity_Id;
      Include_Constants : Boolean) return Name_Sets.Set
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

   begin
      --  ??? Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, instead return empty sets.

      if Ekind (E) in E_Function | E_Procedure | E_Entry
        and then Is_Abstract_Subprogram (E_Alias)
      then
         return Name_Sets.Empty_Set;
      end if;

      Read_Ids := Reads (E_Name);

      if not Include_Constants then
         Read_Ids.Difference (Constants);
      end if;

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

   begin
      --  ??? Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, which do not have effects, instead return the empty set.

      if Ekind (E) in E_Function | E_Procedure | E_Entry
        and then Is_Abstract_Subprogram (E_Alias)
      then
         return Name_Sets.Empty_Set;
      end if;

      --  Go through the reads and check if the entities corresponding to
      --  variables (not constants) have pragma Effective_Reads set. If so,
      --  then these entities are also writes.
      --
      --  ??? call to Computed_Reads repeats what is already done here; this
      --  should be refactored.
      for E_N of Computed_Reads (E, False) loop
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

   -----------------
   -- Is_Constant --
   -----------------

   function Is_Constant (Ent : Entity_Name) return Boolean
     renames Constants.Contains;

   ----------------------------
   -- Is_Protected_Operation --
   ----------------------------

   function Is_Protected_Operation (E_Name : Entity_Name) return Boolean
     renames Protected_Operations.Contains;

   ----------------------
   -- Load_SPARK_Xrefs --
   ----------------------

   procedure Load_SPARK_Xrefs (ALI_Filename : String)
   is
      ALI_File : Ada.Text_IO.File_Type;
      Line     : String (1 .. 1024);
      Last     : Natural;
      Index    : Natural;

      function Getc return Character;
      --  Consume and return next character from Line.
      --  Load next line if at end of line. Return ^Z if at end of file.

      function Nextc return Character;
      --  Peek at next character in Line. Return ^Z if at end of file.

      procedure Skipc;
      --  Skip one character in Line

      ----------
      -- Getc --
      ----------

      function Getc return Character is
         Next_Char : constant Character := Nextc;
      begin
         Index := Index + 1;
         if Index > Last + 1 and then not End_Of_File (ALI_File) then
            Get_Line (ALI_File, Line, Last);
            Index := 1;
         end if;
         return Next_Char;
      end Getc;

      -----------
      -- Nextc --
      -----------

      function Nextc return Character is
      begin
         if Index = Last + 1 then
            return ASCII.LF;

         elsif Index in Line'First .. Last then
            return Line (Index);

         else
            return ASCII.SUB;
         end if;
      end Nextc;

      -----------
      -- Skipc --
      -----------

      procedure Skipc is
         C : Character;
         pragma Unreferenced (C);
      begin
         C := Getc;
      end Skipc;

      procedure Get_SPARK_From_ALI is new Get_SPARK_Xrefs;

   --  Start of processing for Load_SPARK_Xrefs

   begin
      Open (ALI_File, In_File, ALI_Filename);

      --  Skip lines until one that starts with 'F'
      Skip_Non_SPARK_Lines : loop
         if End_Of_File (ALI_File) then
            --  No SPARK cross-reference information in this ALI

            Close (ALI_File);
            return;
         end if;

         Get_Line (ALI_File, Line, Last);
         case Line (1) is
            when 'F' =>
               exit Skip_Non_SPARK_Lines;

            when others =>
               null;
         end case;
      end loop Skip_Non_SPARK_Lines;

      Index := 1;

      Get_SPARK_From_ALI;
      Close (ALI_File);

      --  Walk low-level SPARK tables for this unit and populate high-level
      --  maps.

      Walk_SPARK_Tables : declare

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

      --  Start of processing for Walk_SPARK_Tables

      begin
         --  Fill Scope_Entities : build entity representatives for all scopes
         --  in this ALI file.

         --  Fill Scope_Specs : build a correspondence table between body and
         --  spec scope for the same entity.

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

                  --  Record which entities are scopes, for default
                  --  initializing maps in Propagate_Through_Call_Graph.

                  Scopes.Include (Ent);

                  --  If present, use the body-to-spec information

                  if Srec.Spec_File_Num /= 0 then
                     Scope_Specs.Insert (Sco,
                       Scope_Name'(File_Num  => Srec.Spec_File_Num,
                                   Scope_Num => Srec.Spec_Scope_Num));
                  end if;

                  if Srec.Stype = Xref_Entity_Letters (E_Entry) then
                     Protected_Operations.Include (Ent);
                  end if;
               end;
            end loop;
         end loop;

         --  Fill in high-level tables from xrefs

         Current_Entity := Null_Entity_Name;
         for F in SPARK_File_Table.First ..
                  SPARK_File_Table.Last
         loop
            declare
               Frec : SPARK_File_Record renames SPARK_File_Table.Table (F);

               --  For a subunit, retrieve the file name of the unit instead
               --  of the file name of the subunit, as only unit names are
               --  relevant in the generated Why code.

               File_Entity : constant Entity_Name :=
                 Make_Entity_Name (if Frec.Unit_File_Name /= null
                                   then Frec.Unit_File_Name
                                   else Frec.File_Name);

            begin
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
                              File_Defines.Include (Ref_Entity, File_Entity);
                           end if;

                           --  Register xref according to type

                           case Xref.Rtype is
                           when 'r' =>
                              Add_To_Map (Reads, Ref_Scope_Ent, Ref_Entity);
                           when 'c' =>
                              Constants.Include (Ref_Entity);
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
            end;
         end loop;
      end Walk_SPARK_Tables;
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
     (Ignore_Errors     : Boolean;
      Current_Unit_Only : Boolean := False)
   is

      procedure Propagate_On_Call (Caller, Callee : Entity_Name);
      --  Update reads and writes of subprogram Caller from Callee

      procedure Update_Subprogram (Subp : Entity_Name; Updated : out Boolean);
      --  Update reads and writes of subprogram Subp from its callees

      -----------------------
      -- Propagate_On_Call --
      -----------------------

      procedure Propagate_On_Call (Caller, Callee : Entity_Name) is
         Prop_Reads  : Name_Sets.Set;
         Prop_Writes : Name_Sets.Set;

      begin
         declare
            E : constant Entity_Id := Find_Entity (Callee);
         begin
            --  If Callee has a user-provided Global contract then we use
            --  Get_Proof_Global to work out the Globals from that. Otherwise,
            --  we use the Globals that we gathered from the ALI files.

            if Present (E)
              and then Has_User_Supplied_Globals (E)
            then
               declare
                  Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
                  Write_Ids : Flow_Types.Flow_Id_Sets.Set;
               begin
                  Get_Proof_Globals (Subprogram          => E,
                                     Classwide           => True,
                                     Reads               => Read_Ids,
                                     Writes              => Write_Ids,
                                     Use_Deduced_Globals => False);
                  Prop_Reads  := Flow_Types.To_Name_Set (Read_Ids);
                  Prop_Writes := Flow_Types.To_Name_Set (Write_Ids);
               end;
            else
               Prop_Reads  := Reads (Callee) - Defines (Callee);
               Prop_Writes := Writes (Callee) - Defines (Callee);
            end if;
         end;

         Reads (Caller).Union (Prop_Reads);
         Writes (Caller).Union (Prop_Writes);
      exception
         when Constraint_Error =>
            if Propagate_Error_For_Missing_Scope then
               raise Constraint_Error with
                 ("missing effects for subprogram " &
                     To_String (Callee) &
                     " or subprogram " &
                     To_String (Caller));
            end if;
      end Propagate_On_Call;

      -----------------------
      -- Update_Subprogram --
      -----------------------

      procedure Update_Subprogram (Subp : Entity_Name; Updated : out Boolean)
      is
         Num_Reads   : constant Count_Type := Count_In_Map (Reads, Subp);
         Num_Writes  : constant Count_Type := Count_In_Map (Writes, Subp);
         Called_Subp : Name_Sets.Set renames Calls (Subp);

      begin
         Updated := False;

         --  If Current_Unit_Only is set then we only want the direct
         --  calls and globals.
         if Current_Unit_Only then
            return;
         end if;

         for S of Called_Subp loop
            Propagate_On_Call (Caller => Subp, Callee => S);
         end loop;

         if Num_Reads /= Count_In_Map (Reads, Subp)
           or else Num_Writes /= Count_In_Map (Writes, Subp)
         then
            Updated := True;
         end if;
      exception
         when Constraint_Error =>
            if Propagate_Error_For_Missing_Scope then
               raise Constraint_Error with
                 ("missing effects for subprogram " & To_String (Subp));
            end if;
      end Update_Subprogram;

      Subp_Rest : Name_Sets.Set;

      use Name_Graphs;

   --  Start of processing for Propagate_Through_Call_Graph

   begin
      --  Set error propagation mode for missing scopes

      Propagate_Error_For_Missing_Scope := not Ignore_Errors;

      --  Declare missing scopes, which occurs for generic instantiations (see
      --  K523-007) until a proper treatment of generics. We take into account
      --  all subprograms called.

      for C in Callers.Iterate loop
         Scopes.Include (Key (C));
      end loop;

      --  Initialize the work-set

      for C in Calls.Iterate loop
         Subp_Rest.Insert (Key (C));
      end loop;

      declare
         Cur_SCCs : constant SCCs :=
                      Compute_Strongly_Connected_Components (Subp_Rest);

      begin
         --  Initialize all maps so that each subprogram has an entry in each
         --  map. This is not needed for File_Defines.

         Set_Default_To_Empty (Defines, Scopes);
         Set_Default_To_Empty (Writes,  Scopes);
         Set_Default_To_Empty (Reads,   Scopes);
         Set_Default_To_Empty (Callers, Scopes);
         Set_Default_To_Empty (Calls,   Scopes);

         --  Iterate on SCCs

         for Component of Cur_SCCs loop
            declare
               Continue : Boolean;
               Updated  : Boolean;
            begin
               loop
                  Continue := False;

                  for Node of Component loop
                     Update_Subprogram (Node, Updated);
                     Continue := Continue or else Updated;
                  end loop;
                  exit when not Continue;
               end loop;
            end;
         end loop;
      end;
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
     (Map : in out Name_Graphs.Map;
      Set : Name_Sets.Set)
   is
      Inserted : Boolean;
      Position : Name_Graphs.Cursor;
      --  Dummy variables required by the container API

   begin
      for Ent of Set loop
         Map.Insert (Key      => Ent,
                     Position => Position,
                     Inserted => Inserted);
         --  Attempt to map entity Ent to a default element (i.e. empty set)
      end loop;
   end Set_Default_To_Empty;

   -------------------------------------
   -- Collect_Direct_Computed_Globals --
   -------------------------------------

   procedure Collect_Direct_Computed_Globals
     (E       : Entity_Id;
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

      if Ekind (E) in E_Function | E_Procedure | E_Entry
        and then Is_Abstract_Subprogram (E_Alias)
      then
         --  Initialize to empty sets and return
         Inputs  := Name_Sets.Empty_Set;
         Outputs := Name_Sets.Empty_Set;

         return;
      end if;

      Inputs  := Computed_Reads (E, False);
      Outputs := Computed_Writes (E);

      --  Add variables written to variables read
      --  ??? for composite variables fine, but why for simple ones?
      Inputs.Union (Outputs);
   end Collect_Direct_Computed_Globals;

end SPARK_Frame_Conditions;
