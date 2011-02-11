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

with AA_Util;     use AA_Util;
with Ada.Text_IO; use Ada.Text_IO;
with Atree;       use Atree;
with Einfo;       use Einfo;
with Get_ALFA;
with Namet;       use Namet;
with Sinput;      use Sinput;
with Lib.Xref;

package body ALFA.Frame_Conditions is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Get_Num_For_File (Filename : String) return Nat;
   --  Return a unique number identifying input file Filename

   procedure Set_Default_To_Empty
     (Map : in out Rep_Map.Map;
      Set : Rep_Set.Set);
   --  Make sure each element in Set has an entry in Map. If not already
   --  present, add one which maps the element to the empty set.

   ----------------
   -- Add_To_Map --
   ----------------

   procedure Add_To_Map (Map : in out Rep_Map.Map; From, To : Entity_Rep) is

      procedure Add_To_Set (Ignored : Entity_Rep; Set : in out Rep_Set.Set);
      --  Add entity representative To to set Set

      ----------------
      -- Add_To_Set --
      ----------------

      procedure Add_To_Set (Ignored : Entity_Rep; Set : in out Rep_Set.Set)
      is
         pragma Unreferenced (Ignored);
      begin
         Set.Include (To);
      end Add_To_Set;

   --  Start of processing for Add_To_Map

   begin
      if Map.Contains (From) then
         --  To reactivate when using a different System package than the one
         --  for the compiler, which has a restriction forbidding taking
         --  'Access attribute.

         --  Map.Update_Element (Map.Find (From), Add_To_Set'Access);

         declare
            S : Rep_Set.Set := Map.Element (From);
         begin
            Add_To_Set (From, S);
            Map.Include (From, S);
         end;
      else
         declare
            S : Rep_Set.Set;
         begin
            S.Include (To);
            Map.Insert (From, S);
         end;
      end if;
   end Add_To_Map;

   ----------------
   -- Callers_Of --
   ----------------

   function Callers_Of (Ent : Entity_Rep) return Rep_Set.Set is
   begin
      if Callers.Contains (Ent) then
         return Callers.Element (Ent);
      else
         return Rep_Set.Empty_Set;
      end if;
   end Callers_Of;

   --------------
   -- Calls_Of --
   --------------

   function Calls_Of (Ent : Entity_Rep) return Rep_Set.Set is
   begin
      if Calls.Contains (Ent) then
         return Calls.Element (Ent);
      else
         return Rep_Set.Empty_Set;
      end if;
   end Calls_Of;

   ------------------
   -- Count_In_Map --
   ------------------

   function Count_In_Map
     (Map : Rep_Map.Map;
      Ent : Entity_Rep) return Nat is
   begin
      if Map.Contains (Ent) then
         declare
            Set : constant Rep_Set.Set := Map.Element (Ent);
         begin
            return Nat (Set.Length);
         end;
      else
         return 0;
      end if;
   end Count_In_Map;

   --------------------------
   -- Declare_All_Entities --
   --------------------------

   procedure Declare_All_Entities is

      procedure Declare_Relevant_Entities (N : Node_Id);
      --  Declare entity corresponding to N if relevant, as well as entities
      --  depending on N that would not otherwise be traversed.

      procedure Declare_Relevant_Entities (N : Node_Id) is
         E : Entity_Id;
      begin
         E := Get_Entity_For_Decl (N);

         --  Ignore postcondition procedures which do not define valid
         --  source entities for cross-references.

         if Present (E)
           and then Ekind (E) = E_Procedure
           and then Is_Postcondition_Proc (E)
         then
            return;
         end if;

         --  Ignore entities generated by the compiler, such as objects created
         --  for exceptions declarations.

         if Present (E) and then Comes_From_Source (E) then
            Declare_Entity (E);
         end if;
      end Declare_Relevant_Entities;

   --  Start of processing for Declare_All_Entities

   begin
      Lib.Xref.ALFA.Traverse_All_Compilation_Units
        (Declare_Relevant_Entities'Access);
   end Declare_All_Entities;

   --------------------
   -- Declare_Entity --
   --------------------

   procedure Declare_Entity (E : Entity_Id) is
      Loc   : constant Source_Ptr := Sloc (E);
      Index : constant SFI := Get_Source_File_Index (Loc);
      Name  : constant Unbounded_String :=
                To_Unbounded_String
                  (Name_String (Name_Id (File_Name (Index))));
      Rep   : Entity_Rep;

   begin
      --  ??? Remove the following test when all ALI files are read, in
      --  particular for System.

      if not File_Nums.Contains (Name) then
         return;
      end if;

      Rep := Entity_Rep'(File => File_Nums.Element (Name),
                         Line => Nat (Get_Logical_Line_Number (Loc)),
                         Col  => Nat (Get_Column_Number (Loc)));

      To_AST.Insert (Rep, E);
      From_AST.Insert (E, Rep);
   end Declare_Entity;

   ----------------
   -- Defines_Of --
   ----------------

   function Defines_Of (Ent : Entity_Rep) return Rep_Set.Set is
   begin
      if Defines.Contains (Ent) then
         return Defines.Element (Ent);
      else
         return Rep_Set.Empty_Set;
      end if;
   end Defines_Of;

   ------------------
   -- Display_Maps --
   ------------------

   procedure Display_Maps is

      procedure Display_Entity (E : Entity_Rep);
      procedure Display_One_Map (Map : Rep_Map.Map; Name, Action : String);
      procedure Display_One_Set (Set : Rep_Set.Set);

      --------------------
      -- Display_Entity --
      --------------------

      procedure Display_Entity (E : Entity_Rep) is
         Line_Str : constant String := Nat'Image (E.Line);
         Col_Str  : constant String := Nat'Image (E.Col);
      begin
         Put ("entity @" & To_String (File_Names.Element (E.File))
               & ":" & Line_Str (2 .. Line_Str'Last)
               & ":" & Col_Str (2 .. Col_Str'Last));
      end Display_Entity;

      ---------------------
      -- Display_One_Map --
      ---------------------

      procedure Display_One_Map (Map : Rep_Map.Map; Name, Action : String)
      is
         Cu : Rep_Map.Cursor;
      begin
         Put_Line ("-- " & Name & " --");

         Cu := Map.First;
         while Has_Element (Cu) loop
            Display_Entity (Rep_Map.Key (Cu));
            Put_Line (" " & Action);
            Display_One_Set (Rep_Map.Element (Cu));
            Rep_Map.Next (Cu);
         end loop;
      end Display_One_Map;

      ---------------------
      -- Display_One_Set --
      ---------------------

      procedure Display_One_Set (Set : Rep_Set.Set) is
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

   ----------------------
   -- Get_Num_For_File --
   ----------------------

   function Get_Num_For_File (Filename : String) return Nat is
      Fname : constant Unbounded_String := To_Unbounded_String (Filename);
      Num   : Nat;
   begin
      if File_Nums.Contains (Fname) then
         return File_Nums.Element (Fname);
      else
         Num := Int (File_Nums.Length) + 1;
         File_Nums.Insert (Fname, Num);
         File_Names.Insert (Num, Fname);
         return Num;
      end if;
   end Get_Num_For_File;

   ---------------
   -- Get_Reads --
   ---------------

   procedure Get_Reads
     (E    : Entity_Id;
      Ids  : out Id_Set.Set;
      Reps : out Rep_Set.Set) is
   begin
      Reps := Global_Reads_Of (From_AST.Element (E));

      for C in Reps loop
         if To_AST.Contains (Rep_Set.Element (C)) then
            Ids.Insert (To_AST.Element (Rep_Set.Element (C)));
            Reps.Delete (C);
         end if;
      end loop;
   end Get_Reads;

   ----------------
   -- Get_Writes --
   ----------------

   procedure Get_Writes
     (E    : Entity_Id;
      Ids  : out Id_Set.Set;
      Reps : out Rep_Set.Set) is
   begin
      Reps := Global_Writes_Of (From_AST.Element (E));

      for C in Reps loop
         if To_AST.Contains (Rep_Set.Element (C)) then
            Ids.Insert (To_AST.Element (Rep_Set.Element (C)));
            Reps.Delete (C);
         end if;
      end loop;
   end Get_Writes;

   ---------------------
   -- Global_Reads_Of --
   ---------------------

   function Global_Reads_Of (Ent : Entity_Rep) return Rep_Set.Set is
   begin
      return Reads_Of (Ent) - Defines_Of (Ent);
   end Global_Reads_Of;

   ----------------------
   -- Global_Writes_Of --
   ----------------------

   function Global_Writes_Of (Ent : Entity_Rep) return Rep_Set.Set is
   begin
      return Writes_Of (Ent) - Defines_Of (Ent);
   end Global_Writes_Of;

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

         subtype File_Idx is File_Index range
           ALFA_File_Table.First .. ALFA_File_Table.Last;
         --  Range of indexes in ALFA_File_Table

         type File_Corresp_Array is array (File_Idx) of Nat;
         --  Map each source file to a representative across ALI files

         type Scope_Rep is record
            File_Num  : Nat;
            Scope_Num : Nat;
         end record;
         --  Representative of a scope

         function Scope_Hash (S : Scope_Rep) return Hash_Type is
           (Hash_Type (S.File_Num * 17 + S.Scope_Num));
         --  Hash function for hashed-maps

         package Scope_Entity is new Hashed_Maps
           (Key_Type        => Scope_Rep,
            Element_Type    => Entity_Rep,
            Hash            => Scope_Hash,
            Equivalent_Keys => "=",
            "="             => "=");
         --  Map each scope to its entity representative

         package Scope_Spec is new Hashed_Maps
           (Key_Type        => Scope_Rep,
            Element_Type    => Scope_Rep,
            Hash            => Scope_Hash,
            Equivalent_Keys => "=",
            "="             => "=");
         --  Map body scopes to their spec scope, when different

         File_Corresp   : File_Corresp_Array;
         Scope_Entities : Scope_Entity.Map;
         Scope_Specs    : Scope_Spec.Map;
         Current_Entity : Entity_Rep;

      --  Start of processing for Walk_ALFA_Tables

      begin
         --  Fill File_Corresp : build a table of correspondance between files
         --  in this particular ALI file and numbers across ALI files.

         for F in ALFA_File_Table.First .. ALFA_File_Table.Last loop
            declare
               Frec : ALFA_File_Record renames ALFA_File_Table.Table (F);
            begin
               File_Corresp (F) := Get_Num_For_File (Frec.File_Name.all);
            end;
         end loop;

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
                  Sco  : constant Scope_Rep :=
                           Scope_Rep'(File_Num  => Srec.File_Num,
                                      Scope_Num => Srec.Scope_Num);
                  Ent  : constant Entity_Rep :=
                           Entity_Rep'(File => File_Corresp (F),
                                       Line => Srec.Line,
                                       Col  => Srec.Col);
               begin
                  Scope_Entities.Insert (Sco, Ent);

                  --  If present, use the body-to-spec information

                  if Srec.Spec_File_Num /= 0 then
                     Scope_Specs.Insert (Sco,
                       Scope_Rep'(File_Num  => Srec.Spec_File_Num,
                                  Scope_Num => Srec.Spec_Scope_Num));
                  end if;
               end;
            end loop;
         end loop;

         --  Fill in high-level tables from xrefs

         Current_Entity := Null_Entity;
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

                     Ref_Entity : constant Entity_Rep :=
                                    Entity_Rep'(File => File_Corresp (F),
                                                Line => Xref.Entity_Line,
                                                Col  => Xref.Entity_Col);

                     Ref_Scope     : Scope_Rep;
                     Def_Scope     : Scope_Rep;
                     Ref_Scope_Ent : Entity_Rep;
                     Def_Scope_Ent : Entity_Rep;

                  --  Start of processing for Do_One_Xref

                  begin
                     --  Compute the entity for the scope being referenced

                     Ref_Scope := Scope_Rep'(File_Num  => Xref.File_Num,
                                             Scope_Num => Xref.Scope_Num);
                     if Scope_Specs.Contains (Ref_Scope) then
                        Ref_Scope := Scope_Specs.Element (Ref_Scope);
                     end if;
                     Ref_Scope_Ent := Scope_Entities.Element (Ref_Scope);

                     --  Compute the entity for the scope of the definition

                     Def_Scope := Scope_Rep'(File_Num  => Srec.File_Num,
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
                  end Do_One_Xref;
               end loop;
            end loop;
         end loop;
      end Walk_ALFA_Tables;
   end Load_ALFA;

   ----------------------------------
   -- Propagate_Through_Call_Graph --
   ----------------------------------

   procedure Propagate_Through_Call_Graph is

      procedure Propagate_On_Call (Caller, Callee : Entity_Rep);
      --  Update reads and writes of subprogram Caller from Callee

      procedure Update_Subprogram (Subp : Entity_Rep; Updated : out Boolean);
      --  Update reads and writes of subprogram Subp from its callees

      -----------------------
      -- Propagate_On_Call --
      -----------------------

      procedure Propagate_On_Call (Caller, Callee : Entity_Rep) is
         Prop_Reads  : Rep_Set.Set;
         Prop_Writes : Rep_Set.Set;

         procedure Union_With_Reads
           (Ignored : Entity_Rep;
            Set     : in out Rep_Set.Set);
         --  In place union of caller's reads with the set propagated from
         --  callee.

         procedure Union_With_Writes
           (Ignored : Entity_Rep;
            Set     : in out Rep_Set.Set);
         --  In place union of caller's writes with the set propagated from
         --  callee.

         ----------------------
         -- Union_With_Reads --
         ----------------------

         procedure Union_With_Reads
           (Ignored : Entity_Rep;
            Set     : in out Rep_Set.Set)
         is
            pragma Unreferenced (Ignored);
         begin
            Set.Union (Prop_Reads);
         end Union_With_Reads;

         -----------------------
         -- Union_With_Writes --
         -----------------------

         procedure Union_With_Writes
           (Ignored : Entity_Rep;
            Set     : in out Rep_Set.Set)
         is
            pragma Unreferenced (Ignored);
         begin
            Set.Union (Prop_Writes);
         end Union_With_Writes;

      --  Start of processing for Propagate_On_Call

      begin
         Prop_Reads  := Reads_Of (Callee) - Defines_Of (Callee);
         Prop_Writes := Writes_Of (Callee) - Defines_Of (Callee);

         --  To reactivate when using a different System package than the one
         --  for the compiler, which has a restriction forbidding taking
         --  'Access attribute.

--           Reads.Update_Element
--             (Reads.Find (Caller), Union_With_Reads'Access);
--           Writes.Update_Element
--             (Writes.Find (Caller), Union_With_Writes'Access);

         declare
            S : Rep_Set.Set := Reads.Element (Caller);
         begin
            Union_With_Reads (Caller, S);
            Reads.Include (Caller, S);
         end;

         declare
            S : Rep_Set.Set := Writes.Element (Caller);
         begin
            Union_With_Writes (Caller, S);
            Writes.Include (Caller, S);
         end;
      end Propagate_On_Call;

      -----------------------
      -- Update_Subprogram --
      -----------------------

      procedure Update_Subprogram (Subp : Entity_Rep; Updated : out Boolean) is
         Num_Reads   : Nat;
         Num_Writes  : Nat;
         Called_Subp : Rep_Set.Set;

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

      Work_Set : Rep_Set.Set;
      All_Subp : Rep_Set.Set;
      Cu       : Rep_Map.Cursor;

   --  Start of processing for Propagate_Through_Call_Graph

   begin
      --  Initialize the work-set

      Cu := Calls.First;
      while Has_Element (Cu) loop
         Work_Set.Insert (Key (Cu));
         Next (Cu);
      end loop;

      --  Initialize all maps so that each subprogram has an entry in each map

      Cu := Callers.First;
      while Has_Element (Cu) loop
         All_Subp.Insert (Key (Cu));
         Next (Cu);
      end loop;
      All_Subp.Union (Work_Set);

      Set_Default_To_Empty (Defines, All_Subp);
      Set_Default_To_Empty (Writes, All_Subp);
      Set_Default_To_Empty (Reads, All_Subp);
      Set_Default_To_Empty (Callers, All_Subp);
      Set_Default_To_Empty (Calls, All_Subp);

      --  Iterate through work-set

      while Has_Element (Work_Set.First) loop
         declare
            Cur_Subp : constant Entity_Rep := Element (Work_Set.First);
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

   --------------
   -- Reads_Of --
   --------------

   function Reads_Of (Ent : Entity_Rep) return Rep_Set.Set is
   begin
      if Reads.Contains (Ent) then
         return Reads.Element (Ent);
      else
         return Rep_Set.Empty_Set;
      end if;
   end Reads_Of;

   --------------------------
   -- Set_Default_To_Empty --
   --------------------------

   procedure Set_Default_To_Empty
     (Map : in out Rep_Map.Map;
      Set : Rep_Set.Set)
   is
   begin
      for Ent of Set loop
         if not Map.Contains (Ent) then
            Map.Insert (Ent, Rep_Set.Empty_Set);
         end if;
      end loop;
   end Set_Default_To_Empty;

   ---------------
   -- Writes_Of --
   ---------------

   function Writes_Of (Ent : Entity_Rep) return Rep_Set.Set is
   begin
      if Writes.Contains (Ent) then
         return Writes.Element (Ent);
      else
         return Rep_Set.Empty_Set;
      end if;
   end Writes_Of;

end ALFA.Frame_Conditions;
