------------------------------------------------------------------------------
--                                                                          --
--                         GNAT BACK-END COMPONENTS                         --
--                                                                          --
--                A L F A . F R A M E _ C O N D I T I O N S                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--             Copyright (C) 2011, Free Software Foundation, Inc.           --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Hashed_Maps;
with Ada.Text_IO;                use Ada.Text_IO;

with Get_ALFA;
with Sem_Util;                   use Sem_Util;

package body ALFA.Frame_Conditions is

   -----------------
   -- Local Types --
   -----------------

   package Name_Map is new Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Name_Set.Set,
      Hash            => Name_Hash,
      Equivalent_Keys => Name_Equal,
      "="             => Name_Set."=");
   --  Stores a correspondance between an entity and a set of entities,
   --  where entities are uniquely represented by their name.

   use Name_Map;

   ---------------------
   -- Local Variables --
   ---------------------

   Scopes  : Name_Set.Set;  --  All scope entities

   Defines : Name_Map.Map;  --  Entities defined by each scope
   Writes  : Name_Map.Map;  --  Entities written in each scope
   Reads   : Name_Map.Map;  --  Entities read in each scope
   Callers : Name_Map.Map;  --  Callers for each subprogram
   Calls   : Name_Map.Map;  --  Subprograms called in each subprogram

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Add_To_Map (Map : in out Name_Map.Map; From, To : Entity_Name);
   --  Add the relation From -> To in map Map

   function Count_In_Map
     (Map : Name_Map.Map;
      Ent : Entity_Name) return Nat;
   --  Return the number of elements in the set associated to Ent in Map, or
   --  else 0.

   function Make_Entity_Name (Name : String_Ptr) return Entity_Name
   with Pre => Name /= null and then Name.all /= "";
   --  Build a name for an entity, making sure the name is not empty

   procedure Set_Default_To_Empty
     (Map : in out Name_Map.Map;
      Set : Name_Set.Set);
   --  Make sure each element in Set has an entry in Map. If not already
   --  present, add one which maps the element to the empty set.

   ----------------
   -- Add_To_Map --
   ----------------

   procedure Add_To_Map (Map : in out Name_Map.Map; From, To : Entity_Name) is

      procedure Add_To_Set (Ignored : Entity_Name; Set : in out Name_Set.Set);
      --  Add entity representative To to set Set

      ----------------
      -- Add_To_Set --
      ----------------

      procedure Add_To_Set (Ignored : Entity_Name; Set : in out Name_Set.Set)
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
            S : Name_Set.Set;
         begin
            S.Include (To);
            Map.Insert (From, S);
         end;
      end if;
   end Add_To_Map;

   ------------------
   -- Count_In_Map --
   ------------------

   function Count_In_Map
     (Map : Name_Map.Map;
      Ent : Entity_Name) return Nat is
   begin
      if Map.Contains (Ent) then
         declare
            Set : constant Name_Set.Set := Map.Element (Ent);
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

      procedure Display_Entity (E : Entity_Name);
      procedure Display_One_Map (Map : Name_Map.Map; Name, Action : String);
      procedure Display_One_Set (Set : Name_Set.Set);

      --------------------
      -- Display_Entity --
      --------------------

      procedure Display_Entity (E : Entity_Name) is
      begin
         Put ("entity " & E.all);
      end Display_Entity;

      ---------------------
      -- Display_One_Map --
      ---------------------

      procedure Display_One_Map (Map : Name_Map.Map; Name, Action : String)
      is
         Cu : Name_Map.Cursor;
      begin
         Put_Line ("-- " & Name & " --");

         Cu := Map.First;
         while Has_Element (Cu) loop
            Display_Entity (Name_Map.Key (Cu));
            Put_Line (" " & Action);
            Display_One_Set (Name_Map.Element (Cu));
            Name_Map.Next (Cu);
         end loop;
      end Display_One_Map;

      ---------------------
      -- Display_One_Set --
      ---------------------

      procedure Display_One_Set (Set : Name_Set.Set) is
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

   ---------------
   -- Get_Reads --
   ---------------

   function Get_Reads (E : Entity_Id) return Name_Set.Set is
      Name   : aliased constant String := Unique_Name (E);
      E_Name : constant Entity_Name    :=
                 Make_Entity_Name (Name'Unrestricted_Access);
   begin
      return Reads.Element (E_Name) - Defines.Element (E_Name);
   end Get_Reads;

   ----------------
   -- Get_Writes --
   ----------------

   function Get_Writes (E : Entity_Id) return Name_Set.Set is
      Name   : aliased constant String := Unique_Name (E);
      E_Name : constant Entity_Name    :=
                 Make_Entity_Name (Name'Unrestricted_Access);
   begin
      return Writes.Element (E_Name) - Defines.Element (E_Name);
   end Get_Writes;

   ---------------
   -- Load_ALFA --
   ---------------

   procedure Load_ALFA (ALI_Filename : String) is
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

      procedure Get_ALFA_From_ALI is new Get_ALFA;

   --  Start of processing for Load_ALFA

   begin
      Open (ALI_File, In_File, ALI_Filename);

      Scan_ALI : loop
         if End_Of_File (ALI_File) then
            --  No ALFA information in this ALI

            Close (ALI_File);
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

      Index := 1;

      Get_ALFA_From_ALI;
      Close (ALI_File);

      --  Walk low-level ALFA tables for this unit and populate high-level maps

      Walk_ALFA_Tables : declare

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

      --  Start of processing for Walk_ALFA_Tables

      begin
         --  Fill Scope_Entities : build entity representatives for all scopes
         --  in this ALI file.

         --  Fill Scope_Specs : build a correspondance table between body and
         --  spec scope for the same entity.

         for F in ALFA_File_Table.First .. ALFA_File_Table.Last loop
            for S in ALFA_File_Table.Table (F).From_Scope
              .. ALFA_File_Table.Table (F).To_Scope
            loop
               declare
                  Srec : ALFA_Scope_Record renames ALFA_Scope_Table.Table (S);
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
         for F in ALFA_File_Table.First .. ALFA_File_Table.Last loop
            for S in ALFA_File_Table.Table (F).From_Scope
              .. ALFA_File_Table.Table (F).To_Scope
            loop
               for X in ALFA_Scope_Table.Table (S).From_Xref
                 .. ALFA_Scope_Table.Table (S).To_Xref
               loop
                  Do_One_Xref : declare
                     Srec : ALFA_Scope_Record renames
                              ALFA_Scope_Table.Table (S);
                     Xref : ALFA_Xref_Record renames ALFA_Xref_Table.Table (X);

                     Ref_Entity : constant Entity_Name :=
                                    Make_Entity_Name (Xref.Entity_Name);

                     Ref_Scope     : Scope_Name;
                     Def_Scope     : Scope_Name;
                     Ref_Scope_Ent : Entity_Name;
                     Def_Scope_Ent : Entity_Name;

                  --  Start of processing for Do_One_Xref

                  begin
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

                     --  Register the definition on first occurence

                     if Current_Entity /= Ref_Entity then
                        Add_To_Map (Defines, Def_Scope_Ent, Ref_Entity);
                     end if;

                     --  Register xref according to type

                     case Xref.Rtype is
                        when 'r' =>
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
      end Walk_ALFA_Tables;
   end Load_ALFA;

   ----------------------
   -- Make_Entity_Name --
   ----------------------

   function Make_Entity_Name (Name : String_Ptr) return Entity_Name is
     (Entity_Name (Name));

   ----------------------------------
   -- Propagate_Through_Call_Graph --
   ----------------------------------

   procedure Propagate_Through_Call_Graph is

      procedure Propagate_On_Call (Caller, Callee : Entity_Name);
      --  Update reads and writes of subprogram Caller from Callee

      procedure Update_Subprogram (Subp : Entity_Name; Updated : out Boolean);
      --  Update reads and writes of subprogram Subp from its callees

      -----------------------
      -- Propagate_On_Call --
      -----------------------

      procedure Propagate_On_Call (Caller, Callee : Entity_Name) is
         Prop_Reads  : Name_Set.Set;
         Prop_Writes : Name_Set.Set;

         procedure Union_With_Reads
           (Ignored : Entity_Name;
            Set     : in out Name_Set.Set);
         --  In place union of caller's reads with the set propagated from
         --  callee.

         procedure Union_With_Writes
           (Ignored : Entity_Name;
            Set     : in out Name_Set.Set);
         --  In place union of caller's writes with the set propagated from
         --  callee.

         ----------------------
         -- Union_With_Reads --
         ----------------------

         procedure Union_With_Reads
           (Ignored : Entity_Name;
            Set     : in out Name_Set.Set)
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
            Set     : in out Name_Set.Set)
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
      end Propagate_On_Call;

      -----------------------
      -- Update_Subprogram --
      -----------------------

      procedure Update_Subprogram (Subp : Entity_Name; Updated : out Boolean)
      is
         Num_Reads   : Nat;
         Num_Writes  : Nat;
         Called_Subp : Name_Set.Set;

      begin
         Num_Reads  := Count_In_Map (Reads, Subp);
         Num_Writes := Count_In_Map (Writes, Subp);

         Updated := False;

         Called_Subp := Calls.Element (Subp);

         for S of Called_Subp loop
            Propagate_On_Call (Caller => Subp, Callee => S);
         end loop;

         if Num_Reads /= Count_In_Map (Reads, Subp)
           or else Num_Writes /= Count_In_Map (Writes, Subp)
         then
            Updated := True;
         end if;
      end Update_Subprogram;

      Work_Set : Name_Set.Set;
      Cu       : Name_Map.Cursor;

   --  Start of processing for Propagate_Through_Call_Graph

   begin
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
         Work_Set.Insert (Key (Cu));
         Next (Cu);
      end loop;

      --  Initialize all maps so that each subprogram has an entry in each map

      Set_Default_To_Empty (Defines, Scopes);
      Set_Default_To_Empty (Writes,  Scopes);
      Set_Default_To_Empty (Reads,   Scopes);
      Set_Default_To_Empty (Callers, Scopes);
      Set_Default_To_Empty (Calls,   Scopes);

      --  Iterate through work-set

      while Has_Element (Work_Set.First) loop
         declare
            Cur_Subp : constant Entity_Name := Element (Work_Set.First);
            Updated  : Boolean;
         begin
            Work_Set.Delete (Cur_Subp);
            Update_Subprogram (Cur_Subp, Updated);

            if Updated then
               Work_Set.Union (Callers.Element (Cur_Subp));
            end if;
         end;
      end loop;

   end Propagate_Through_Call_Graph;

   --------------------------
   -- Set_Default_To_Empty --
   --------------------------

   procedure Set_Default_To_Empty
     (Map : in out Name_Map.Map;
      Set : Name_Set.Set)
   is
   begin
      for Ent of Set loop
         if not Map.Contains (Ent) then
            Map.Insert (Ent, Name_Set.Empty_Set);
         end if;
      end loop;
   end Set_Default_To_Empty;

end ALFA.Frame_Conditions;
