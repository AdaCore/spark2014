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

with Ada.Text_IO;       use Ada.Text_IO;
with Get_ALFA;

package body ALFA.Frame_Conditions is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Get_Num_For_File (Filename : String) return Nat;
   --  Return a unique number identifying input file Filename

   ----------------
   -- Add_To_Map --
   ----------------

   procedure Add_To_Map (Map : in out Entity_Map.Map; From, To : Entity_Rep) is

      procedure Add_To_Set (Ignored : Entity_Rep; Set : in out Entity_Set.Set);
      --  Add entity representative To to set Set

      ----------------
      -- Add_To_Set --
      ----------------

      procedure Add_To_Set (Ignored : Entity_Rep; Set : in out Entity_Set.Set)
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
            S : Entity_Set.Set := Map.Element (From);
         begin
            Add_To_Set (From, S);
            Map.Include (From, S);
         end;
      else
         declare
            S : Entity_Set.Set;
         begin
            S.Include (To);
            Map.Insert (From, S);
         end;
      end if;
   end Add_To_Map;

   ------------------
   -- Display_Maps --
   ------------------

   procedure Display_Maps is

      procedure Display_Entity (E : Entity_Rep);
      procedure Display_One_Map (Map : Entity_Map.Map; Name, Action : String);
      procedure Display_One_Set (Set : Entity_Set.Set);

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

      procedure Display_One_Map (Map : Entity_Map.Map; Name, Action : String)
      is
         Cu : Entity_Map.Cursor;
         use type Entity_Map.Cursor;
      begin
         Put_Line ("-- " & Name & " --");

         Cu := Map.First;
         while Cu /= Entity_Map.No_Element loop
            Display_Entity (Entity_Map.Key (Cu));
            Put_Line (" " & Action);
            Display_One_Set (Entity_Map.Element (Cu));
            Entity_Map.Next (Cu);
         end loop;
      end Display_One_Map;

      ---------------------
      -- Display_One_Set --
      ---------------------

      procedure Display_One_Set (Set : Entity_Set.Set) is
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
   -- Load_ALFA --
   ---------------

   procedure Load_ALFA (ALI_Filename : String) is
      ALI_File : File_Type;
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

      --  Walk low-level ALFA table for this unit and populate high-level maps

      declare
         subtype File_Idx is File_Index range
           ALFA_File_Table.First .. ALFA_File_Table.Last;
         type File_Corresp_Array is array (File_Idx) of Nat;

         type Scope_Rep is record
            File_Num  : Nat;
            Scope_Num : Nat;
         end record;

         function Scope_Hash (S : Scope_Rep) return Hash_Type is
           (Hash_Type (S.File_Num * 17 + S.Scope_Num));

         package Scope_Map is new Hashed_Maps
           (Key_Type        => Scope_Rep,
            Element_Type    => Entity_Rep,
            Hash            => Scope_Hash,
            Equivalent_Keys => "=",
            "="             => "=");

         File_Corresp   : File_Corresp_Array;
         Scope_Entities : Scope_Map.Map;
         Current_Entity : Entity_Rep;

      begin
         --  Build a table of correspondance between files in this particular
         --  ALI file and numbers across ALI files.

         for F in ALFA_File_Table.First .. ALFA_File_Table.Last loop
            declare
               Frec : ALFA_File_Record renames ALFA_File_Table.Table (F);
            begin
               File_Corresp (F) := Get_Num_For_File (Frec.File_Name.all);
            end;
         end loop;

         --  Build entity representatives for all scopes in this ALI file

         for F in ALFA_File_Table.First .. ALFA_File_Table.Last loop
            for S in ALFA_File_Table.Table (F).From_Scope
              .. ALFA_File_Table.Table (F).To_Scope
            loop
               declare
                  Srec : ALFA_Scope_Record renames ALFA_Scope_Table.Table (S);
               begin
                  Scope_Entities.Insert (
                    Scope_Rep'(File_Num  => Srec.File_Num,
                               Scope_Num => Srec.Scope_Num),
                    Entity_Rep'(File => File_Corresp (F),
                                Line => Srec.Line,
                                Col  => Srec.Col));
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
                  declare
                     Srec : ALFA_Scope_Record renames
                              ALFA_Scope_Table.Table (S);
                     Xref : ALFA_Xref_Record renames ALFA_Xref_Table.Table (X);

                     Ref_Entity : constant Entity_Rep :=
                                    Entity_Rep'(File => File_Corresp (F),
                                                Line => Xref.Entity_Line,
                                                Col  => Xref.Entity_Col);
                     Ref_Scope  : constant Entity_Rep :=
                                    Scope_Entities.Element
                                      (Scope_Rep'(File_Num => Xref.File_Num,
                                                 Scope_Num => Xref.Scope_Num));
                     Def_Scope  : constant Entity_Rep :=
                                    Scope_Entities.Element
                                      (Scope_Rep'(File_Num => Srec.File_Num,
                                                 Scope_Num => Srec.Scope_Num));
                  begin
                     if Current_Entity /= Ref_Entity then
                        Add_To_Map (Defines, Def_Scope, Ref_Entity);
                     end if;

                     case Xref.Rtype is
                        when 'r' =>
                           Add_To_Map (Reads, Ref_Scope, Ref_Entity);
                        when 'm' =>
                           Add_To_Map (Writes, Ref_Scope, Ref_Entity);
                        when 's' =>
                           Add_To_Map (Calls, Ref_Scope, Ref_Entity);
                           Add_To_Map (Callers, Ref_Entity, Ref_Scope);
                        when others =>
                           raise Program_Error;
                     end case;
                  end;
               end loop;
            end loop;
         end loop;
      end;
   end Load_ALFA;

end ALFA.Frame_Conditions;
