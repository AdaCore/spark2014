------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                S P A R K _ F R A M E _ C O N D I T I O N S               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2011-2013, AdaCore                     --
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

with Ada.Text_IO;            use Ada.Text_IO;
with Unchecked_Deallocation;

with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Get_SPARK_Xrefs;
with Output;                 use Output;
with Sem_Aux;                use Sem_Aux;
with Sem_Util;               use Sem_Util;
with Snames;                 use Snames;
with SPARK_Xrefs;            use SPARK_Xrefs;

with SPARK_Util;             use SPARK_Util;

with Gnat2Why.Nodes;         use Gnat2Why.Nodes;

package body SPARK_Frame_Conditions is

   -----------------
   -- Local Types --
   -----------------

   type Id is mod 2 ** 32;
   --  Representation of an entity

   function Id_Hash (X : Id) return Hash_Type is (Hash_Type (X));

   package Id_Set is new Hashed_Sets
     (Element_Type        => Id,
      Hash                => Id_Hash,
      Equivalent_Elements => "=",
      "="                 => "=");
   use Id_Set;

   package Id_Map is new Hashed_Maps
     (Key_Type        => Id,
      Element_Type    => Id_Set.Set,
      Hash            => Id_Hash,
      Equivalent_Keys => "=",
      "="             => "=");
   use Id_Map;

   package Id_To_Name_Map is new Hashed_Maps
     (Key_Type        => Id,
      Element_Type    => Entity_Name,
      Hash            => Id_Hash,
      Equivalent_Keys => "=",
      "="             => Name_Equal);
   use Id_To_Name_Map;

   package Name_To_Id_Map is new Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Id,
      Hash            => Name_Hash,
      Equivalent_Keys => Name_Equal,
      "="             => "=");
   use Name_To_Id_Map;

   package Value_Map is new Hashed_Maps
     (Key_Type        => Id,
      Element_Type    => Integer,
      Hash            => Id_Hash,
      Equivalent_Keys => "=",
      "="             => "=");
   --  Map used internally in strongly connected component computation. Not to
   --  be confused with map over ids.

   package Name_To_Entity_Map is new Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Entity_Id,
      Hash            => Name_Hash,
      Equivalent_Keys => Name_Equal,
      "="             => "=");

   Name_To_Entity : Name_To_Entity_Map.Map := Name_To_Entity_Map.Empty_Map;

   type SCC is array (Positive range <>) of Id;
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

   Entity_Ids : Name_To_Id_Map.Map;    --  Map name to id
   Entity_Names : Id_To_Name_Map.Map;  --  Map id to name

   Scopes  : Id_Set.Set;  --  All scope entities

   File_Defines : Name_Map.Map;  --  File defining each entities
   Defines      : Id_Map.Map;  --  Entities defined by each scope
   Writes       : Id_Map.Map;  --  Entities written in each scope
   Reads        : Id_Map.Map;  --  Entities read in each scope
   Callers      : Id_Map.Map;  --  Callers for each subprogram
   Calls        : Id_Map.Map;  --  Subprograms called in each subprogram

   Next_Id : Id := 1;     --  Next available identity

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Add_To_Map (Map : in out Id_Map.Map; From, To : Id);
   --  Add the relation From -> To in map Map

   function Compute_Strongly_Connected_Components
     (Nodes : Id_Set.Set) return SCCs;
   --  Computation of strongly connected components from Tarjan. Individual
   --  components are dynamically allocated.

   function Count_In_Map
     (Map : Id_Map.Map;
      Ent : Id) return Nat;
   --  Return the number of elements in the set associated to Ent in Map, or
   --  else 0.

   procedure Free_SCCs (X : SCCs);
   --  Free memory allocated for strongly connected components

   function Id_Of_Entity (E : Entity_Name) return Id;
   --  Return integer identity for name, and create it if necessary

   function Make_Entity_Name (Name : String_Ptr) return Entity_Name
   with Pre => Name /= null and then Name.all /= "";
   --  Build a name for an entity, making sure the name is not empty

   procedure Set_Default_To_Empty
     (Map : in out Id_Map.Map;
      Set : Id_Set.Set);
   --  Make sure each element in Set has an entry in Map. If not already
   --  present, add one which maps the element to the empty set.

   function To_Names (Ids : Id_Set.Set) return Name_Set.Set;
   --  Convert set of identities to set of names

   ----------------
   -- Add_To_Map --
   ----------------

   procedure Add_To_Map (Map : in out Id_Map.Map; From, To : Id) is

      procedure Add_To_Set (Ignored : Id; Set : in out Id_Set.Set);
      --  Add entity representative To to set Set

      ----------------
      -- Add_To_Set --
      ----------------

      procedure Add_To_Set (Ignored : Id; Set : in out Id_Set.Set)
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
            S : Id_Set.Set;
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
     (Nodes : Id_Set.Set) return SCCs
   is
      subtype Node_Range is Integer range 1 .. Integer (Nodes.Length);

      --  There are at most as many SCCs as nodes (if no recursion at all)

      Cur_SCCs     : SCCs (Node_Range);
      Cur_SCCs_Num : Natural := 0;

      Indexes  : Value_Map.Map;
      Lowlinks : Value_Map.Map;

      Index : Natural := 1;

      -----------------------
      -- Local Subprograms --
      -----------------------

      procedure Strong_Connect (V : Id);
      --  Compute SCC for V, possibly generating other reachable SCCs before
      --  returning.

      --------------------
      -- Stack of nodes --
      --------------------

      type Stack_Data is array (Node_Range) of Id;
      type Stack is record
         Data    : Stack_Data;
         Content : Id_Set.Set;
      end record;

      S : Stack;
      S_Size : Natural := 0;

      procedure Push (E : Id);
      function Peer (Lookahead : Natural) return Id;
      function Pop return Id;
      function Has (E : Id) return Boolean;

      procedure Push (E : Id) is
      begin
         S_Size := S_Size + 1;
         S.Data (S_Size) := E;
         S.Content.Include (E);
      end Push;

      function Pop return Id is
         E : constant Id := S.Data (S_Size);
      begin
         S_Size := S_Size - 1;
         S.Content.Delete (E);
         return E;
      end Pop;

      function Peer (Lookahead : Natural) return Id is
      begin
         return S.Data (S_Size - Lookahead);
      end Peer;

      function Has (E : Id) return Boolean is
      begin
         return S.Content.Contains (E);
      end Has;

      --------------------
      -- Strong_Connect --
      --------------------

      procedure Strong_Connect (V : Id) is
         Called_Subp : Id_Set.Set;
      begin
         --  Set the depth index for V to the smallest unused index

         Indexes.Include (V, Index);
         Lowlinks.Include (V, Index);
         Index := Index + 1;
         Push (V);

         --  Consider successors of V

         Called_Subp := Calls.Element (V);

--  Workaround for K526-008

--           for W of Called_Subp loop
--              ...
--           end loop;

         declare
            C : Id_Set.Cursor;
            W : Id;
         begin
            C := Called_Subp.First;
            while C /= Id_Set.No_Element loop
               W := Element (C);

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

               Next (C);
            end loop;
         end;

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

   begin
--  Workaround for K526-008

--           for V of Nodes loop
--              if not Indexes.Contains (V) then
--                 Strong_Connect (V);
--              end if;
--           end loop;

      declare
         C : Id_Set.Cursor;
      begin
         C := Nodes.First;
         while C /= Id_Set.No_Element loop
            if not Indexes.Contains (Element (C)) then
               Strong_Connect (Element (C));
            end if;
            Next (C);
         end loop;
      end;

      return Cur_SCCs (1 .. Cur_SCCs_Num);
   end Compute_Strongly_Connected_Components;

   ------------------
   -- Count_In_Map --
   ------------------

   function Count_In_Map
     (Map : Id_Map.Map;
      Ent : Id) return Nat is
   begin
      if Map.Contains (Ent) then
         declare
            Set : constant Id_Set.Set := Map.Element (Ent);
         begin
            return Nat (Set.Length);
         end;
      else
         return 0;
      end if;
   end Count_In_Map;

   ------------------
   -- Display_Maps --
   ------------------

   procedure Display_Maps is

      procedure Display_Entity (E : Id);
      procedure Display_One_Map (Map : Id_Map.Map; Name, Action : String);
      procedure Display_One_Set (Set : Id_Set.Set);

      --------------------
      -- Display_Entity --
      --------------------

      procedure Display_Entity (E : Id) is
      begin
         Put ("entity " & Entity_Names.Element (E).all);
      end Display_Entity;

      ---------------------
      -- Display_One_Map --
      ---------------------

      procedure Display_One_Map (Map : Id_Map.Map; Name, Action : String)
      is
         Cu : Id_Map.Cursor;
      begin
         Put_Line ("-- " & Name & " --");

         Cu := Map.First;
         while Has_Element (Cu) loop
            Display_Entity (Id_Map.Key (Cu));
            Put_Line (" " & Action);
            Display_One_Set (Id_Map.Element (Cu));
            Id_Map.Next (Cu);
         end loop;
      end Display_One_Map;

      ---------------------
      -- Display_One_Set --
      ---------------------

      procedure Display_One_Set (Set : Id_Set.Set) is
      begin
--  Workaround for K526-008

--           for Ent of Set loop
--              Put ("  "); Display_Entity (Ent); Put_Line ("");
--           end loop;

         declare
            C : Id_Set.Cursor;
         begin
            C := Set.First;
            while C /= Id_Set.No_Element loop
               Put ("  "); Display_Entity (Element (C)); Put_Line ("");
               Next (C);
            end loop;
         end;
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

   ------------------------
   -- Find_Object_Entity --
   ------------------------

   function Find_Object_Entity (E : Entity_Name) return Entity_Id is
      use Name_To_Entity_Map;
      C : constant Name_To_Entity_Map.Cursor := Name_To_Entity.Find (E);
   begin
      if Has_Element (C) then
         return Element (C);
      else
         return Empty;
      end if;
   end Find_Object_Entity;

   ------------------------------
   -- For_All_External_Objects --
   ------------------------------

   procedure For_All_External_Objects
     (Process : not null access procedure (E : Entity_Name))
   is

      procedure For_All_Define_Sets (Key : Id; S : Id_Set.Set);
      --  will be called for all "define sets" for all subprograms

      -------------------------
      -- For_All_Define_Sets --
      -------------------------

      procedure For_All_Define_Sets (Key : Id; S : Id_Set.Set)
      is
         pragma Unreferenced (Key);
      begin
         for Elt of S loop
            declare
               E : constant Entity_Name := Entity_Names.Element (Elt);
               C : constant Name_Set.Cursor :=
                 Translated_Object_Entities.Find (E);
            begin
               if not (Name_Set.Has_Element (C)) then
                  Process (E);
               end if;
            end;
         end loop;
      end For_All_Define_Sets;

      --  beginning of processing for For_All_External_Objects
   begin
      for C in Defines.Iterate loop
         Id_Map.Query_Element (C, For_All_Define_Sets'Access);
      end loop;
   end For_All_External_Objects;

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

   ---------------
   -- Get_Reads --
   ---------------

   function Get_Reads (E : Entity_Id) return Name_Set.Set is
      E_Alias : constant Entity_Id :=
        (if Present (Alias (E)) then Ultimate_Alias (E) else E);
      Name    : aliased constant String := Unique_Name (E_Alias);
      E_Name  : constant Entity_Name    :=
        Make_Entity_Name (Name'Unrestricted_Access);
      E_Id    : Id;
      Read_Ids : Id_Set.Set := Id_Set.Empty_Set;
      Global_Node : constant Node_Id := Get_Pragma (E_Alias, Pragma_Global);

   begin
      --  Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, which do not have effects, instead return the empty set.

      if Is_Abstract_Subprogram (E_Alias) then
         return Name_Set.Empty_Set;
      end if;

      E_Id := Entity_Ids.Element (E_Name);

      if Present (Global_Node) then
         declare
            Reads  : Node_Sets.Set;
            Writes : Node_Sets.Set;
         begin
            Get_Global_Items (Global_Node,
                              Reads  => Reads,
                              Writes => Writes);
            for R of Reads loop
               --  References to constant objects are not considered in SPARK
               --  section, as these will be translated as constants in the
               --  intermediate language for formal verification, and should
               --  therefore never appear in frame conditions.

               if not Is_Constant_Object (R) then
                  declare
                     Name    : aliased constant String := Unique_Name (R);
                     R_Name  : constant Entity_Name    :=
                       Make_Entity_Name (Name'Unrestricted_Access);
                  begin
                     Read_Ids.Include (Entity_Ids.Element (R_Name));
                  end;
               end if;
            end loop;
         end;
      else
         Read_Ids := Reads.Element (E_Id);
      end if;

      return To_Names (Read_Ids - Defines.Element (E_Id));
   exception
      when Constraint_Error =>
         if Propagate_Error_For_Missing_Scope then
            raise Constraint_Error with
              ("missing effects for subprogram " & Name);
         else
            return Name_Set.Empty_Set;
         end if;
   end Get_Reads;

   ----------------
   -- Get_Writes --
   ----------------

   function Get_Writes (E : Entity_Id) return Name_Set.Set is
      E_Alias : constant Entity_Id :=
        (if Present (Alias (E)) then Ultimate_Alias (E) else E);
      Name    : aliased constant String := Unique_Name (E_Alias);
      E_Name  : constant Entity_Name    :=
        Make_Entity_Name (Name'Unrestricted_Access);
      E_Id    : Id;
      Write_Ids : Id_Set.Set := Id_Set.Empty_Set;
      Global_Node : constant Node_Id := Get_Pragma (E_Alias, Pragma_Global);

   begin
      --  Abstract subprograms not yet supported. Avoid issuing an error on
      --  those, which do not have effects, instead return the empty set.

      if Is_Abstract_Subprogram (E_Alias) then
         return Name_Set.Empty_Set;
      end if;

      E_Id := Entity_Ids.Element (E_Name);

      if Present (Global_Node) then
         declare
            Reads  : Node_Sets.Set;
            Writes : Node_Sets.Set;
         begin
            Get_Global_Items (Global_Node,
                              Reads  => Reads,
                              Writes => Writes);
            for W of Writes loop
               declare
                  Name    : aliased constant String := Unique_Name (W);
                  W_Name  : constant Entity_Name    :=
                    Make_Entity_Name (Name'Unrestricted_Access);
               begin
                  Write_Ids.Include (Entity_Ids.Element (W_Name));
               end;
            end loop;
         end;
      else
         Write_Ids := Writes.Element (E_Id);
      end if;

      return To_Names (Write_Ids - Defines.Element (E_Id));
   exception
      when Constraint_Error =>
         if Propagate_Error_For_Missing_Scope then
            raise Constraint_Error with
              ("missing effects for subprogram " & Name);
         else
            return Name_Set.Empty_Set;
         end if;
   end Get_Writes;

   ------------------
   -- Id_Of_Entity --
   ------------------

   function Id_Of_Entity (E : Entity_Name) return Id is
      This_Id : Id;
   begin
      if Entity_Ids.Contains (E) then
         return Entity_Ids.Element (E);
      else
         This_Id := Next_Id;
         Entity_Ids.Include (E, This_Id);
         Entity_Names.Include (This_Id, E);
         Next_Id := Next_Id + 1;
         return This_Id;
      end if;
   end Id_Of_Entity;

   ----------------------
   -- Is_Heap_Variable --
   ----------------------

   function Is_Heap_Variable (Ent : Entity_Name) return Boolean is
      (Ent.all = SPARK_Xrefs.Name_Of_Heap_Variable);

   ----------------------
   -- Load_SPARK_Xrefs --
   ----------------------

   procedure Load_SPARK_Xrefs (ALI_Filename : String) is
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
            Write_Str ("error:" & ALI_Filename &
                         " does not contain SPARK Xrefs section");
            Write_Eol;

            raise Terminate_Program;
         end if;

         Get_Line (ALI_File, Line, Last);
         case Line (1) is
            when 'F' =>
               exit Scan_ALI;

            when others =>
               null;
         end case;
      end loop Scan_ALI;

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
         --  Nameresentative of a scope

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

         --  Fill Scope_Specs : build a correspondance table between body and
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

                  Scopes.Include (Id_Of_Entity (Ent));

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
                       and then Xref.Rtype in 'r' | 'm'
                     then
                        Add_To_Map (Defines,
                                    Id_Of_Entity (Def_Scope_Ent),
                                    Id_Of_Entity (Ref_Entity));
                        File_Defines.Include (Ref_Entity, File_Entity);
                     end if;

                     --  Register xref according to type

                     case Xref.Rtype is
                        when 'r' =>
                           Add_To_Map (Reads,
                                       Id_Of_Entity (Ref_Scope_Ent),
                                       Id_Of_Entity (Ref_Entity));
                        when 'm' =>
                           Add_To_Map (Writes,
                                       Id_Of_Entity (Ref_Scope_Ent),
                                       Id_Of_Entity (Ref_Entity));
                        when 's' =>
                           Add_To_Map (Calls,
                                       Id_Of_Entity (Ref_Scope_Ent),
                                       Id_Of_Entity (Ref_Entity));
                           Add_To_Map (Callers,
                                       Id_Of_Entity (Ref_Entity),
                                       Id_Of_Entity (Ref_Scope_Ent));
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
     (Entity_Name (Name));

   ----------------------------------
   -- Propagate_Through_Call_Graph --
   ----------------------------------

   procedure Propagate_Through_Call_Graph (Ignore_Errors : Boolean) is

      procedure Propagate_On_Call (Caller, Callee : Id);
      --  Update reads and writes of subprogram Caller from Callee

      procedure Update_Subprogram (Subp : Id; Updated : out Boolean);
      --  Update reads and writes of subprogram Subp from its callees

      -----------------------
      -- Propagate_On_Call --
      -----------------------

      procedure Propagate_On_Call (Caller, Callee : Id) is
         Prop_Reads  : Id_Set.Set;
         Prop_Writes : Id_Set.Set;

         procedure Union_With_Reads
           (Ignored : Id;
            Set     : in out Id_Set.Set);
         --  In place union of caller's reads with the set propagated from
         --  callee.

         procedure Union_With_Writes
           (Ignored : Id;
            Set     : in out Id_Set.Set);
         --  In place union of caller's writes with the set propagated from
         --  callee.

         ----------------------
         -- Union_With_Reads --
         ----------------------

         procedure Union_With_Reads
           (Ignored : Id;
            Set     : in out Id_Set.Set)
         is
            pragma Unreferenced (Ignored);
         begin
            Set.Union (Prop_Reads);
         end Union_With_Reads;

         -----------------------
         -- Union_With_Writes --
         -----------------------

         procedure Union_With_Writes
           (Ignored : Id;
            Set     : in out Id_Set.Set)
         is
            pragma Unreferenced (Ignored);
         begin
            Set.Union (Prop_Writes);
         end Union_With_Writes;

      --  Start of processing for Propagate_On_Call

      begin
         Prop_Reads  := Reads.Element (Callee) - Defines.Element (Callee);
         Prop_Writes := Writes.Element (Callee) - Defines.Element (Callee);

         Reads.Update_Element
           (Reads.Find (Caller), Union_With_Reads'Access);
         Writes.Update_Element
           (Writes.Find (Caller), Union_With_Writes'Access);
      exception
         when Constraint_Error =>
            if Propagate_Error_For_Missing_Scope then
               raise Constraint_Error with
                 ("missing effects for subprogram " &
                     Entity_Names.Element (Callee).all &
                     " or subprogram " &
                     Entity_Names.Element (Caller).all);
            end if;
      end Propagate_On_Call;

      -----------------------
      -- Update_Subprogram --
      -----------------------

      procedure Update_Subprogram (Subp : Id; Updated : out Boolean)
      is
         Num_Reads   : Nat;
         Num_Writes  : Nat;
         Called_Subp : Id_Set.Set;

      begin
         Num_Reads  := Count_In_Map (Reads, Subp);
         Num_Writes := Count_In_Map (Writes, Subp);

         Updated := False;

         Called_Subp := Calls.Element (Subp);

--  Workaround for K526-008

--           for S of Called_Subp loop
--              Propagate_On_Call (Caller => Subp, Callee => S);
--           end loop;

         declare
            C : Id_Set.Cursor;
         begin
            C := Called_Subp.First;
            while C /= Id_Set.No_Element loop
               Propagate_On_Call (Caller => Subp, Callee => Element (C));
               Next (C);
            end loop;
         end;

         if Num_Reads /= Count_In_Map (Reads, Subp)
           or else Num_Writes /= Count_In_Map (Writes, Subp)
         then
            Updated := True;
         end if;
      exception
         when Constraint_Error =>
            if Propagate_Error_For_Missing_Scope then
               raise Constraint_Error with
                 ("missing effects for subprogram " &
                     Entity_Names.Element (Subp).all);
            end if;
      end Update_Subprogram;

      Cu        : Id_Map.Cursor;
      Subp_Rest : Id_Set.Set;

   --  Start of processing for Propagate_Through_Call_Graph

   begin
      --  Set error propagation mode for missing scopes

      Propagate_Error_For_Missing_Scope := not Ignore_Errors;

      --  Declare missing scopes, which occurs for generic instanciations (see
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

   ----------------------------
   -- Register_Object_Entity --
   ----------------------------

   procedure Register_Object_Entity (E : Entity_Id) is
      E_Name : constant Entity_Name := new String'(Unique_Name (E));
   begin
      Name_To_Entity.Include (E_Name, E);
   end Register_Object_Entity;

   --------------------------
   -- Set_Default_To_Empty --
   --------------------------

   procedure Set_Default_To_Empty
     (Map : in out Id_Map.Map;
      Set : Id_Set.Set)
   is
   begin
--  Workaround for K526-008
--        for Ent of Set loop
--           if not Map.Contains (Ent) then
--              Map.Insert (Ent, Name_Set.Empty_Set);
--           end if;
--        end loop;

      declare
         C : Id_Set.Cursor;
      begin
         C := Set.First;
         while C /= Id_Set.No_Element loop
            if not Map.Contains (Element (C)) then
               Map.Insert (Element (C), Id_Set.Empty_Set);
            end if;
            Next (C);
         end loop;
      end;
   end Set_Default_To_Empty;

   -----------------------
   -- Set_Ignore_Errors --
   -----------------------

   procedure Set_Ignore_Errors (Ignore_Errors : Boolean) is
   begin
      Propagate_Error_For_Missing_Scope := not Ignore_Errors;
   end Set_Ignore_Errors;

   --------------
   -- To_Names --
   --------------

   function To_Names (Ids : Id_Set.Set) return Name_Set.Set is
      Names : Name_Set.Set;
      C : Id_Set.Cursor;
   begin
      C := Ids.First;
      while C /= Id_Set.No_Element loop
         Names.Include (Entity_Names.Element (Element (C)));
         Next (C);
      end loop;
      return Names;
   end To_Names;

end SPARK_Frame_Conditions;
