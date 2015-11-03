------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                S P A R K _ F R A M E _ C O N D I T I O N S               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2011-2015, AdaCore                     --
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
with Ada.Text_IO;                use Ada.Text_IO;
with Flow_Generated_Globals;     use Flow_Generated_Globals;
with Flow_Types;                 use Flow_Types;
with Flow_Utility;               use Flow_Utility;
with Fname.UF;
with Get_SPARK_Xrefs;
with Lib;
with Osint;
with Sem_Aux;                    use Sem_Aux;
with Snames;                     use Snames;
with SPARK_Xrefs;                use SPARK_Xrefs;
with Unchecked_Deallocation;
with Uname;

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

   type SCC is array (Positive range <>) of Entity_Name;
   --  Ordered list of subprograms in a strongly connected component, roughly
   --  ordered so as to follow call chains for better propagation.

   type SCC_Ptr is access SCC;
   type SCCs is array (Positive range <>) of SCC_Ptr;
   --  Ordered list of strongly connected components in call-graph, with the
   --  "leaf" SCCs coming first.

   ---------------------
   -- Local Variables --
   ---------------------

   Propagate_Error_For_Missing_Scope : Boolean := True;
   --  By default, propagate an error if a scope is missing, unless set to
   --  False for a degraded mode of operation in which such errors are ignored.

   Scopes       : Name_Sets.Set;  --  All scope entities
   Constants    : Name_Sets.Set;  --  All constants

   File_Defines : Name_Maps.Map;    --  File defining each entities
   Defines      : Name_Graphs.Map;  --  Entities defined by each scope
   Writes       : Name_Graphs.Map;  --  Entities written in each scope
   Reads        : Name_Graphs.Map;  --  Entities read in each scope
   Callers      : Name_Graphs.Map;  --  Callers for each subprogram
   Calls        : Name_Graphs.Map;  --  Subprograms called in each subprogram

   Non_Rec_Subp : Name_Sets.Set;
   --  All non-recursive subprograms containing at least one call

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Add_To_Map (Map : in out Name_Graphs.Map; From, To : Entity_Name);
   --  Add the relation From -> To in map Map

   function Compute_Strongly_Connected_Components
     (Nodes : Name_Sets.Set) return SCCs;
   --  Computation of strongly connected components from Tarjan. Individual
   --  components are dynamically allocated.

   function Count_In_Map
     (Map : Name_Graphs.Map;
      Ent : Entity_Name) return Count_Type;
   --  Return the number of elements in the set associated to Ent in Map, or
   --  else 0.

   procedure Free_SCCs (X : SCCs);
   --  Free memory allocated for strongly connected components

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

      procedure Add_To_Set (Ignored : Entity_Name; Set : in out Name_Sets.Set);
      --  Add entity representative To to set Set

      ----------------
      -- Add_To_Set --
      ----------------

      procedure Add_To_Set (Ignored : Entity_Name; Set : in out Name_Sets.Set)
      is
         pragma Unreferenced (Ignored);
      begin
         Set.Include (To);
      end Add_To_Set;

   --  Start of processing for Add_To_Map

   begin
      if Map.Contains (From) then
         Map.Update_Element (Map.Find (From), Add_To_Set'Access);
      else
         declare
            S : Name_Sets.Set;
         begin
            S.Include (To);
            Map.Insert (From, S);
         end;
      end if;
   end Add_To_Map;

   -------------------------------------------
   -- Compute_Strongly_Connected_Components --
   -------------------------------------------

   function Compute_Strongly_Connected_Components
     (Nodes : Name_Sets.Set) return SCCs
   is
      subtype Node_Range is Integer range 1 .. Integer (Nodes.Length);

      --  There are at most as many SCCs as nodes (if no recursion at all)

      Cur_SCCs     : SCCs (Node_Range);
      Cur_SCCs_Num : Natural := 0;

      package Value_Map is new Hashed_Maps
        (Key_Type        => Entity_Name,
         Element_Type    => Integer,
         Hash            => Name_Hash,
         Equivalent_Keys => "=",
         "="             => "=");
      --  Map used internally in strongly connected component computation. Not
      --  to be confused with map over ids.

      Indexes  : Value_Map.Map;
      Lowlinks : Value_Map.Map;

      Index : Natural := 1;

      -----------------------
      -- Local Subprograms --
      -----------------------

      procedure Strong_Connect (V : Entity_Name);
      --  Compute SCC for V, possibly generating other reachable SCCs before
      --  returning.

      --------------------
      -- Stack of nodes --
      --------------------

      type Stack_Data is array (Node_Range) of Entity_Name;
      type Stack is record
         Data    : Stack_Data;
         Content : Name_Sets.Set;
      end record;

      S : Stack;
      S_Size : Natural := 0;

      procedure Push (E : Entity_Name);
      function Peer (Lookahead : Natural) return Entity_Name;
      function Pop return Entity_Name;
      function Has (E : Entity_Name) return Boolean;

      procedure Push (E : Entity_Name) is
      begin
         S_Size := S_Size + 1;
         S.Data (S_Size) := E;
         S.Content.Include (E);
      end Push;

      function Pop return Entity_Name is
         E : constant Entity_Name := S.Data (S_Size);
      begin
         S_Size := S_Size - 1;
         S.Content.Delete (E);
         return E;
      end Pop;

      function Peer (Lookahead : Natural) return Entity_Name is
      begin
         return S.Data (S_Size - Lookahead);
      end Peer;

      function Has (E : Entity_Name) return Boolean is
      begin
         return S.Content.Contains (E);
      end Has;

      --------------------
      -- Strong_Connect --
      --------------------

      procedure Strong_Connect (V : Entity_Name) is
         Called_Subp : Name_Sets.Set;
      begin
         --  Set the depth index for V to the smallest unused index

         Indexes.Include (V, Index);
         Lowlinks.Include (V, Index);
         Index := Index + 1;
         Push (V);

         --  Consider successors of V

         Called_Subp := Calls.Element (V);

         for W of Called_Subp loop
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

         if Lowlinks.Element (V) = Indexes.Element (V) then
            declare
               function Size_Of_Current_SCC return Positive;
               --  Return the size of the current SCC sitting on the stack

               -------------------------
               -- Size_Of_Current_SCC --
               -------------------------

               function Size_Of_Current_SCC return Positive is
                  Size : Natural := 0;
               begin
                  while Peer (Size) /= V loop
                     Size := Size + 1;
                  end loop;
                  return Size + 1;
               end Size_Of_Current_SCC;

               --  Start a new strongly connected component

               Cur_SCC : constant SCC_Ptr :=
                           new SCC (1 .. Size_Of_Current_SCC);

            begin
               for J in Cur_SCC'Range loop
                  Cur_SCC (J) := Pop;
               end loop;

               pragma Assert (Cur_SCC (Cur_SCC'Last) = V);

               --  Output the current strongly connected component

               Cur_SCCs_Num := Cur_SCCs_Num + 1;
               Cur_SCCs (Cur_SCCs_Num) := Cur_SCC;
            end;
         end if;
      end Strong_Connect;

   --  Start of processing for Compute_Strongly_Connected_Components

   begin

      for V of Nodes loop
         if not Indexes.Contains (V) then
            Strong_Connect (V);
         end if;
      end loop;

      return Cur_SCCs (1 .. Cur_SCCs_Num);
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
              then Name_Graphs.Element (C).Length
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
         Cu : Name_Graphs.Cursor;
      begin
         Put_Line ("-- " & Name & " --");

         Cu := Map.First;
         while Has_Element (Cu) loop
            Display_Entity (Name_Graphs.Key (Cu));
            Put_Line (" " & Action);
            Display_One_Set (Name_Graphs.Element (Cu));
            Name_Graphs.Next (Cu);
         end loop;
      end Display_One_Map;

      ---------------------
      -- Display_One_Set --
      ---------------------

      procedure Display_One_Set (Set : Name_Sets.Set) is
      begin
         for Ent of Set loop
            Put ("  "); Display_Entity (Ent); Put_Line ("");
         end loop;
      end Display_One_Set;

   --  Start of processing for Display_Maps

   begin
      Display_One_Map (Defines, "Variables defined by subprograms", "defines");
      Put_Line ("");
      Display_One_Map (Reads, "Variables read by subprograms", "reads");
      Put_Line ("");
      Display_One_Map (Writes, "Variables written by subprograms", "writes");
      Put_Line ("");
      Display_One_Map (Calls, "Subprograms called", "calls");
      Put_Line ("");
      Display_One_Map (Callers, "Callers of subprograms", "is called by");
   end Display_Maps;

   --------------------
   -- File_Of_Entity --
   --------------------

   function File_Of_Entity (E : Entity_Name) return Entity_Name is
   begin
      return File_Defines.Element (E);
   end File_Of_Entity;

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
      procedure For_All_Define_Sets (Key : Entity_Name; S : Name_Sets.Set);
      --  will be called for all "define sets" for all subprograms

      -------------------------
      -- For_All_Define_Sets --
      -------------------------

      procedure For_All_Define_Sets (Key : Entity_Name; S : Name_Sets.Set) is
         pragma Unreferenced (Key);
      begin
         --  External objects are those in the sets of defined objects Defines,
         --  that are not constant objects from the set Constants.

         for Elt of S loop
            if not Constants.Contains (Elt) then
               declare
                  C : constant Name_Sets.Cursor :=
                    Translated_Object_Entities.Find (Elt);
               begin
                  if not (Name_Sets.Has_Element (C)) then
                     Process (Elt);
                  end if;
               end;
            end if;
         end loop;
      end For_All_Define_Sets;

   --  Start of processing for For_All_External_Objects

   begin
      for C in Defines.Iterate loop
         Name_Graphs.Query_Element (C, For_All_Define_Sets'Access);
      end loop;
   end For_All_External_Objects;

   -----------------------------
   -- For_All_External_States --
   -----------------------------

   procedure For_All_External_States
     (Process : not null access procedure (E : Entity_Name))
   is
   begin
      for State_Name of GG_Get_All_State_Abstractions loop
         --  Any state abstraction for which we do NOT have a
         --  corresponding Entidy_Id is an External state abstraction.

         if not Present (Find_Entity (State_Name)) then
            Process (State_Name);
         end if;
      end loop;
   end For_All_External_States;

   ---------------
   -- Free_SCCs --
   ---------------

   procedure Free_SCCs (X : SCCs) is
      procedure Free is new Unchecked_Deallocation (SCC, SCC_Ptr);
      Tmp : SCC_Ptr;
   begin
      for J in X'Range loop
         Tmp := X (J);
         Free (Tmp);
      end loop;
   end Free_SCCs;

   --------------------
   -- Computed_Calls --
   --------------------

   function Computed_Calls (E_Name : Entity_Name) return Name_Sets.Set
   is (Calls.Element (E_Name));

   -------------------------
   -- Get_Generated_Reads --
   -------------------------

   function Get_Generated_Reads
     (E                 : Entity_Id;
      Include_Constants : Boolean) return Name_Sets.Set
   is
      E_Alias  : constant Entity_Id :=
        (if Present (Alias (E)) then Ultimate_Alias (E) else E);
      E_Name   : constant Entity_Name := To_Entity_Name (E_Alias);
      Read_Ids : Name_Sets.Set := Name_Sets.Empty_Set;

   begin
      --  ??? O429-046, O603-033 Task types, entries and Abstract subprograms
      --  not yet supported. Avoid issuing an error on those, instead return
      --  empty sets.

      if Ekind (E) in Task_Kind | Entry_Kind then
         return Name_Sets.Empty_Set;
      end if;

      --  Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, which do not have effects, instead return the empty set.

      if Is_Abstract_Subprogram (E_Alias) then
         return Name_Sets.Empty_Set;
      end if;

      Read_Ids := Reads.Element (E_Name);

      if not Include_Constants then
         Read_Ids := Read_Ids - Constants;
      end if;

      return Read_Ids - Defines.Element (E_Name);
   exception
      when Constraint_Error =>
         if Propagate_Error_For_Missing_Scope then
            raise Constraint_Error with
              ("missing effects for subprogram " & To_String (E_Name));
         else
            return Name_Sets.Empty_Set;
         end if;
   end Get_Generated_Reads;

   --------------------------
   -- Get_Generated_Writes --
   --------------------------

   function Get_Generated_Writes (E : Entity_Id) return Name_Sets.Set is
      E_Alias   : constant Entity_Id :=
        (if Present (Alias (E)) then Ultimate_Alias (E) else E);
      E_Name    : constant Entity_Name := To_Entity_Name (E_Alias);
      Write_Ids : Name_Sets.Set := Name_Sets.Empty_Set;

   begin
      --  ??? O429-046, O603-033 Task types, entries and Abstract subprograms
      --  not yet supported. Avoid issuing an error on those, instead return
      --  empty sets.

      if Ekind (E) in Task_Kind | Entry_Kind then
         return Name_Sets.Empty_Set;
      end if;

      --  Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, which do not have effects, instead return the empty set.

      if Is_Abstract_Subprogram (E_Alias) then
         return Name_Sets.Empty_Set;
      end if;

      --  Go through the reads and check if the entities corresponding to
      --  variables (not constants) have pragma Effective_Reads set. If so,
      --  then these entities are also writes.

      for E_N of Get_Generated_Reads (E, False) loop
         declare
            Read : constant Entity_Id := Find_Entity (E_N);
         begin
            if Present (Read)
              and then Ekind (Read) = E_Variable
              and then Present (Get_Pragma (Read, Pragma_Effective_Reads))
            then
               Write_Ids.Insert (E_N);
            end if;
         end;
      end loop;

      Write_Ids := Write_Ids or Writes.Element (E_Name);

      return Write_Ids - Defines.Element (E_Name);
   exception
      when Constraint_Error =>
         if Propagate_Error_For_Missing_Scope then
            raise Constraint_Error with
              ("missing effects for subprogram " & To_String (E_Name));
         else
            return Name_Sets.Empty_Set;
         end if;
   end Get_Generated_Writes;

   -------------------------
   -- Has_Computed_Global --
   -------------------------

   --  A Global contract is computed for E whenever the corresponding ALI file
   --  has been loaded.

   function Has_Computed_Global (E : Entity_Id) return Boolean is

      --  The code for retrieving the right name for the ALI file is similar
      --  to the one printing 'W' lines in ALI files (see lib-writ.adb), which
      --  needs to deal with non-standard naming schemes.

      U : Unit_Name_Type;
      Body_Fname : File_Name_Type;
      ALI_File_Name : File_Name_Type;

   begin
      --  Compute the name of the ALI file containing the local effects of
      --  subprogram E.

      U := Lib.Unit_Name (Lib.Get_Source_Unit (E));

      if Uname.Is_Spec_Name (U) then
         Body_Fname :=
           Fname.UF.Get_File_Name
             (Uname.Get_Body_Name (U),
              Subunit => False, May_Fail => True);

         if Body_Fname = No_File then
            Body_Fname := Fname.UF.Get_File_Name (U, Subunit => False);
         end if;

      else
         Body_Fname := Fname.UF.Get_File_Name (U, Subunit => False);
      end if;

      ALI_File_Name := Osint.Lib_File_Name (Body_Fname);

      --  Effects were computed for subprogram E iff the ALI file with its
      --  local effects was loaded.

      return Loaded_ALI_Files.Contains (ALI_File_Name);
   end Has_Computed_Global;

   ----------------------
   -- Is_Heap_Variable --
   ----------------------

   function Is_Heap_Variable (Ent : Entity_Name) return Boolean is
      (To_String (Ent) = SPARK_Xrefs.Name_Of_Heap_Variable);

   -----------------
   -- Is_Constant --
   -----------------

   function Is_Constant (Ent : Entity_Name) return Boolean is
      (Constants.Contains (Ent));

   ---------------------------------
   -- Is_Non_Recursive_Subprogram --
   ---------------------------------

   function Is_Non_Recursive_Subprogram (E : Entity_Id) return Boolean is
      E_Alias  : constant Entity_Id :=
        (if Present (Alias (E)) then Ultimate_Alias (E) else E);
      E_Name   : constant Entity_Name := To_Entity_Name (E);
   begin
      --  Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, instead return false.

      if Is_Abstract_Subprogram (E_Alias) then
         return False;
      end if;

      --  A subprogram is non-recursive if either it contains no call or its
      --  Entity_Name has been stored in Non_Rec_Subp.

      return Calls.Element (E_Name).Is_Empty
        or else Non_Rec_Subp.Contains (E_Name);
   end Is_Non_Recursive_Subprogram;

   ----------------------
   -- Load_SPARK_Xrefs --
   ----------------------

   procedure Load_SPARK_Xrefs
     (ALI_Filename    : String;
      Has_SPARK_Xrefs : out Boolean)
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
            return Character'Val (16#1a#);
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

      Scan_ALI : loop
         if End_Of_File (ALI_File) then
            --  No SPARK cross-reference information in this ALI

            Close (ALI_File);
            Has_SPARK_Xrefs := False;
            return;
         end if;

         Get_Line (ALI_File, Line, Last);
         case Line (1) is
            when 'F' =>
               exit Scan_ALI;

            when others =>
               null;
         end case;
      end loop Scan_ALI;

      Has_SPARK_Xrefs := True;
      Index := 1;

      Get_SPARK_From_ALI;
      Close (ALI_File);

      --  Walk low-level SPARK tables for this unit and populate high-level
      --  maps.

      Walk_SPARK_Tables : declare

         type Scope_Name is record
            File_Num  : Nat;
            Scope_Num : Nat;
         end record;
         --  Name representative of a scope

         function Scope_Hash (S : Scope_Name) return Hash_Type is
           (Hash_Type (S.File_Num * 17 + S.Scope_Num));
         --  Hash function for hashed-maps

         package Scope_Entity is new Hashed_Maps
           (Key_Type        => Scope_Name,
            Element_Type    => Entity_Name,
            Hash            => Scope_Hash,
            Equivalent_Keys => "=",
            "="             => "=");
         --  Map each scope to its entity representative

         package Scope_Spec is new Hashed_Maps
           (Key_Type        => Scope_Name,
            Element_Type    => Scope_Name,
            Hash            => Scope_Hash,
            Equivalent_Keys => "=",
            "="             => "=");
         --  Map body scopes to their spec scope, when different

         Scope_Entities : Scope_Entity.Map;
         Scope_Specs    : Scope_Spec.Map;
         Current_Entity : Entity_Name;

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
               end;
            end loop;
         end loop;

         --  Fill in high-level tables from xrefs

         Current_Entity := Null_Entity_Name;
         for F in SPARK_File_Table.First .. SPARK_File_Table.Last loop
            for S in SPARK_File_Table.Table (F).From_Scope
              .. SPARK_File_Table.Table (F).To_Scope
            loop
               for X in SPARK_Scope_Table.Table (S).From_Xref
                 .. SPARK_Scope_Table.Table (S).To_Xref
               loop
                  Do_One_Xref : declare
                     Frec : SPARK_File_Record renames
                              SPARK_File_Table.Table (F);
                     Srec : SPARK_Scope_Record renames
                              SPARK_Scope_Table.Table (S);
                     Xref : SPARK_Xref_Record renames
                              SPARK_Xref_Table.Table (X);

                     File_Entity : Entity_Name;
                     Ref_Entity : constant Entity_Name :=
                                     Make_Entity_Name (Xref.Entity_Name);

                     Ref_Scope     : Scope_Name;
                     Def_Scope     : Scope_Name;
                     Ref_Scope_Ent : Entity_Name;
                     Def_Scope_Ent : Entity_Name;

                  --  Start of processing for Do_One_Xref

                  begin

                     --  For a subunit, retrieve the file name of the unit
                     --  instead of the file name of the subunit, as only unit
                     --  names are relevant in the generated Why code.

                     if Frec.Unit_File_Name /= null then
                        File_Entity := Make_Entity_Name (Frec.Unit_File_Name);
                     else
                        File_Entity := Make_Entity_Name (Frec.File_Name);
                     end if;

                     --  Compute the entity for the scope being referenced

                     Ref_Scope := Scope_Name'(File_Num  => Xref.File_Num,
                                              Scope_Num => Xref.Scope_Num);
                     if Scope_Specs.Contains (Ref_Scope) then
                        Ref_Scope := Scope_Specs.Element (Ref_Scope);
                     end if;
                     Ref_Scope_Ent := Scope_Entities.Element (Ref_Scope);

                     --  Compute the entity for the scope of the definition

                     Def_Scope := Scope_Name'(File_Num  => Srec.File_Num,
                                              Scope_Num => Srec.Scope_Num);
                     if Scope_Specs.Contains (Def_Scope) then
                        Def_Scope := Scope_Specs.Element (Def_Scope);
                     end if;
                     Def_Scope_Ent := Scope_Entities.Element (Def_Scope);

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
            end loop;
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

         procedure Union_With_Reads
           (Ignored : Entity_Name;
            Set     : in out Name_Sets.Set);
         --  In place union of caller's reads with the set propagated from
         --  callee.

         procedure Union_With_Writes
           (Ignored : Entity_Name;
            Set     : in out Name_Sets.Set);
         --  In place union of caller's writes with the set propagated from
         --  callee.

         ----------------------
         -- Union_With_Reads --
         ----------------------

         procedure Union_With_Reads
           (Ignored : Entity_Name;
            Set     : in out Name_Sets.Set)
         is
            pragma Unreferenced (Ignored);
         begin
            Set.Union (Prop_Reads);
         end Union_With_Reads;

         -----------------------
         -- Union_With_Writes --
         -----------------------

         procedure Union_With_Writes
           (Ignored : Entity_Name;
            Set     : in out Name_Sets.Set)
         is
            pragma Unreferenced (Ignored);
         begin
            Set.Union (Prop_Writes);
         end Union_With_Writes;

      --  Start of processing for Propagate_On_Call

      begin
         declare
            E : constant Entity_Id := Find_Entity (Callee);
         begin
            --  If Callee has a user-provided Global contract then we use
            --  Get_Proof_Global to work out the Globals from that. Otherwise,
            --  we use the Globals that we gathered from the ALI files.

            if Present (E)
              and then (Present (Get_Pragma (E, Pragma_Global)) or else
                          Present (Get_Pragma (E, Pragma_Depends)))
            then
               declare
                  Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
                  Write_Ids : Flow_Types.Flow_Id_Sets.Set;
               begin
                  Get_Proof_Globals (Subprogram           => E,
                                     Classwide            => True,
                                     Reads                => Read_Ids,
                                     Writes               => Write_Ids,
                                     Use_Computed_Globals => False);
                  Prop_Reads  := Flow_Types.To_Name_Set (Read_Ids);
                  Prop_Writes := Flow_Types.To_Name_Set (Write_Ids);
               end;
            else
               Prop_Reads  :=
                 Reads.Element (Callee) - Defines.Element (Callee);
               Prop_Writes :=
                 Writes.Element (Callee) - Defines.Element (Callee);
            end if;
         end;

         Reads.Update_Element
           (Reads.Find (Caller), Union_With_Reads'Access);
         Writes.Update_Element
           (Writes.Find (Caller), Union_With_Writes'Access);
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
         Called_Subp : constant Name_Sets.Set := Calls.Element (Subp);

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

      Cu        : Name_Graphs.Cursor;
      Subp_Rest : Name_Sets.Set;

      use Name_Graphs;

   --  Start of processing for Propagate_Through_Call_Graph

   begin
      --  Set error propagation mode for missing scopes

      Propagate_Error_For_Missing_Scope := not Ignore_Errors;

      --  Declare missing scopes, which occurs for generic instantiations (see
      --  K523-007) until a proper treatment of generics. We take into account
      --  all subprograms called.

      Cu := Callers.First;
      while Has_Element (Cu) loop
         Scopes.Include (Key (Cu));
         Next (Cu);
      end loop;

      --  Initialize the work-set

      Cu := Calls.First;
      while Has_Element (Cu) loop
         Subp_Rest.Insert (Key (Cu));
         Next (Cu);
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

         --  Collect non-recursive subprograms
         --  A subprogram is non-recursive if it is alone in its strongly
         --  connected component and if it does not call itself directly.

         for J in Cur_SCCs'Range loop
            if Cur_SCCs (J)'Length = 1 then
               declare
                  E : constant Entity_Name := Cur_SCCs (J) (1);
               begin
                  if not Name_Sets.Contains (Calls.Element (E), E) then
                     Non_Rec_Subp.Insert (E);
                  end if;
               end;
            end if;
         end loop;

         --  Iterate on SCCs

         for J in Cur_SCCs'Range loop
            declare
               Continue : Boolean := True;
               Updated  : Boolean;
            begin
               while Continue loop
                  Continue := False;

                  for K in Cur_SCCs (J)'Range loop
                     Update_Subprogram (Cur_SCCs (J) (K), Updated);
                     Continue := Continue or else Updated;
                  end loop;
               end loop;
            end;
         end loop;

         Free_SCCs (Cur_SCCs);
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
     (E                  : Entity_Id;
      Inputs             : out Name_Sets.Set;
      Outputs            : out Name_Sets.Set;
      Called_Subprograms : out Name_Sets.Set)
   is
      E_Alias : Entity_Id;
      E_Name  : Entity_Name;

   begin

      --  Initialize to empty sets
      Inputs             := Name_Sets.Empty_Set;
      Outputs            := Name_Sets.Empty_Set;
      Called_Subprograms := Name_Sets.Empty_Set;

      --  ??? O429-046, O603-033 Task types, entries and Abstract subprograms
      --  not yet supported. Avoid issuing an error on those, instead return
      --  empty sets.

      if Ekind (E) in Task_Kind | Entry_Kind then
         return;
      end if;

      E_Alias := (if Present (Alias (E)) then Ultimate_Alias (E) else E);

      if Is_Abstract_Subprogram (E_Alias) then
         return;
      end if;

      E_Name  := To_Entity_Name (E_Alias);

      Called_Subprograms := Calls.Element (E_Name);
      Inputs             := Get_Generated_Reads (E, False);
      Outputs            := Get_Generated_Writes (E);

      --  Add variables written to variables read
      Inputs.Union (Outputs);
   end Collect_Direct_Computed_Globals;

   -----------------------
   -- Set_Ignore_Errors --
   -----------------------

   procedure Set_Ignore_Errors (Ignore_Errors : Boolean) is
   begin
      Propagate_Error_For_Missing_Scope := not Ignore_Errors;
   end Set_Ignore_Errors;

end SPARK_Frame_Conditions;
