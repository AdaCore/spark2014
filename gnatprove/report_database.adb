------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        R E P O R T _ D A T A B A S E                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Ordered_Sets;

with GNATCOLL.Utils;

with Hash_Cons;

package body Report_Database is

   Symbol_Table : constant Symbol_Table_Access := Allocate;

   function Hash (S : Subp_Type_Rec) return Ada.Containers.Hash_Type;

   ----------
   -- Hash --
   ----------

   function Hash (S : Subp_Type_Rec) return Ada.Containers.Hash_Type is
      use Ada.Containers;
   begin
      return 3 * Hash (S.Name) + 5 * Hash (S.File) + 7 * Hash_Type (S.Line);
   end Hash;

   package Unique_Subps is new
     Hash_Cons (Elt_Type    => Subp_Type_Rec,
                Access_Type => Subp_Type,
                Hash        => Hash,
                "="         => "=");

   package Subp_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Subp_Type,
        Element_Type    => Stat_Rec,
        Hash            => Unique_Subps.Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   Default_Stat : constant Stat_Rec :=
     Stat_Rec'(SPARK         => False,
               Analysis      => No_Analysis,
               Suppr_Msgs    => Warning_Lists.Empty_List,
               Flow_Warnings => 0,
               Flow_Errors   => 0,
               VC_Count      => 0,
               VC_Proved     => 0);

   function "<" (Left, Right : Symbol) return Boolean is
     (Get (Left, Empty_If_Null => True).all <
        Get (Right, Empty_If_Null => True).all);

   function "<" (Left, Right : Subp_Type) return Boolean is
     (if Left.File < Right.File then True
      elsif Right.File < Left.File then False
      elsif Left.Name < Right.Name then True
      elsif Right.Name < Left.Name then False
      else Left.Line < Right.Line);

   package Ordered_Subp_Sets is new
     Ada.Containers.Ordered_Sets (Element_Type => Subp_Type,
                                  "<"          => "<");

   package Unit_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Unit_Type,
        Element_Type    => Subp_Maps.Map,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => Subp_Maps."=");

   function "<" (Left, Right : Unit_Type) return Boolean is
     (Symbol (Left) < Symbol (Right));

   package Ordered_Unit_Sets is new
     Ada.Containers.Ordered_Sets (Element_Type => Unit_Type,
                                  "<"          => "<");

   Unit_Map : Unit_Maps.Map := Unit_Maps.Empty_Map;

   procedure Update_Subp_Entry
     (Unit    : Unit_Type;
      Subp    : Subp_Type;
      Process : not null access procedure (Stat : in out Stat_Rec));
   --  update the stat record of the given subp using the callback. If the
   --  unit/subp didn't exist yet, they are added, and a default Stat_Rec
   --  is created.

   ---------------------
   -- Add_Flow_Result --
   ---------------------

   procedure Add_Flow_Result
     (Unit  : Unit_Type;
      Subp  : Subp_Type;
      Error : Boolean)
   is
      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         if Error then
            Stat.Flow_Errors := Stat.Flow_Errors + 1;
         else
            Stat.Flow_Warnings := Stat.Flow_Warnings + 1;
         end if;
      end Process;

   --  Start of Add_Flow_Result

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_Flow_Result;

   ----------------------
   -- Add_Proof_Result --
   ----------------------

   procedure Add_Proof_Result
     (Unit   : Unit_Type;
      Subp   : Subp_Type;
      Proved : Boolean)
   is
      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.VC_Count := Stat.VC_Count + 1;
         if Proved then
            Stat.VC_Proved := Stat.VC_Proved + 1;
         end if;
      end Process;

   --  Start of Add_Proof_Result

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_Proof_Result;

   ----------------------
   -- Add_SPARK_Status --
   ----------------------

   procedure Add_SPARK_Status
     (Unit         : Unit_Type;
      Subp         : Subp_Type;
      SPARK_Status : Boolean;
      Analysis     : Analysis_Status) is

      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.SPARK := SPARK_Status;
         Stat.Analysis := Analysis;
      end Process;

   --  Start of Add_SPARK_Status

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_SPARK_Status;

   ---------------------
   -- Add_Flow_Result --
   ---------------------

   procedure Add_Suppressed_Warning
     (Unit   : Unit_Type;
      Subp   : Subp_Type;
      Reason : String;
      File   : String;
      Line   : Integer;
      Column : Integer)
   is
      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.Suppr_Msgs.Append
           (Suppressed_Warning'(Reason => To_Unbounded_String (Reason),
                                File   => To_Unbounded_String (File),
                                Line   => Line,
                                Column => Column));
      end Process;

   --  Start of Add_Flow_Result

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_Suppressed_Warning;

   ----------------
   -- Iter_Subps --
   ----------------

   procedure Iter_All_Subps
     (Process : not null access
                   procedure (U : Unit_Type;
                              Subp : Subp_Type;
                              Stat : Stat_Rec))
   is
      procedure Iter_Subp_Map (Unit : Unit_Type; Map : Subp_Maps.Map);

      -------------------
      -- Iter_Subp_Map --
      -------------------

      procedure Iter_Subp_Map (Unit : Unit_Type; Map : Subp_Maps.Map) is
         use Subp_Maps;
      begin
         for Subp_C in Map.Iterate loop
            Process (Unit, Key (Subp_C), Element (Subp_C));
         end loop;
      end Iter_Subp_Map;

      use Unit_Maps;

      --  beginning of processing for Iter_Subps

   begin
      for Unit_C in Unit_Map.Iterate loop
         Query_Element (Unit_C, Iter_Subp_Map'Access);
      end loop;
   end Iter_All_Subps;

   ----------------
   -- Iter_Units --
   ----------------

   procedure Iter_Units
     (Process : not null access procedure (U : Unit_Type);
      Ordered : Boolean := False) is
   begin
      --  To iterate over units in the order of their names, first insert all
      --  unit symbols in an ordered set, and then iterate over this ordered
      --  set.

      if Ordered then
         declare
            use Ordered_Unit_Sets;
            Names : Set;
         begin
            for Unit_C in Unit_Map.Iterate loop
               Names.Include (Unit_Maps.Key (Unit_C));
            end loop;

            for Unit of Names loop
               Process (Unit);
            end loop;
         end;

      --  Otherwise, directly iterate over map of units

      else
         for Unit_C in Unit_Map.Iterate loop
            Process (Unit_Maps.Key (Unit_C));
         end loop;
      end if;
   end Iter_Units;

   ---------------------
   -- Iter_Unit_Subps --
   ---------------------

   procedure Iter_Unit_Subps
     (Unit    : Unit_Type;
      Process : not null access procedure (Subp : Subp_Type; Stat : Stat_Rec);
      Ordered : Boolean := False)
   is
      procedure Iter_Subp_Map (Unit : Unit_Type; Map : Subp_Maps.Map);

      -------------------
      -- Iter_Subp_Map --
      -------------------

      procedure Iter_Subp_Map (Unit : Unit_Type; Map : Subp_Maps.Map) is
         pragma Unreferenced (Unit);
      begin
         --  To iterate over subprograms in the order of their names, first
         --  insert all subprogram symbols in an ordered set, and then iterate
         --  over this ordered set.

         if Ordered then
            declare
               use Ordered_Subp_Sets;
               Names : Set;
            begin
               for Subp_C in Map.Iterate loop
                  Names.Include (Subp_Maps.Key (Subp_C));
               end loop;

               for Subp of Names loop
                  Process (Subp, Subp_Maps.Element (Map, Subp));
               end loop;
            end;

         --  Otherwise, directly iterate over map of units

         else
            for Subp_C in Map.Iterate loop
               Process (Subp_Maps.Key (Subp_C), Subp_Maps.Element (Subp_C));
            end loop;
         end if;
      end Iter_Subp_Map;

      C : constant Unit_Maps.Cursor := Unit_Map.Find (Unit);

      --  beginning of processing for Iter_Unit_Subps

   begin
      if Unit_Maps.Has_Element (C) then
         Unit_Maps.Query_Element (C, Iter_Subp_Map'Access);
      end if;
   end Iter_Unit_Subps;

   -------------
   -- Mk_Unit --
   -------------

   function Mk_Unit (Name : String) return Unit_Type is
      S : constant Symbol := Find (Symbol_Table, Name);
   begin
      return Unit_Type (S);
   end Mk_Unit;

   -------------
   -- Mk_Subp --
   -------------

   function Mk_Subp (Name : String; File : String; Line : Integer)
                     return Subp_Type is
   begin
      return
        Unique_Subps.Hash_Cons
          (Subp_Type_Rec'(Name => Find (Symbol_Table, Name),
                          File => Find (Symbol_Table, File),
                          Line => Line));
   end Mk_Subp;

   ---------------
   -- Num_Subps --
   ---------------

   function Num_Subps (Unit : Unit_Type) return Integer is

      Count : aliased Integer := 0;

      procedure Update (Subp : Subp_Type; Stat : Stat_Rec);

      procedure Update (Subp : Subp_Type; Stat : Stat_Rec) is
         pragma Unreferenced (Subp, Stat);
      begin
         Count := Count + 1;
      end Update;

   begin
      Iter_Unit_Subps (Unit, Update'Access);
      return Count;
   end Num_Subps;

   ---------------------
   -- Num_Subps_SPARK --
   ---------------------

   function Num_Subps_SPARK (Unit : Unit_Type) return Integer
   is
      Count : aliased Integer := 0;

      procedure Update (Subp : Subp_Type; Stat : Stat_Rec);

      procedure Update (Subp : Subp_Type; Stat : Stat_Rec) is
         pragma Unreferenced (Subp);
      begin
         if Stat.SPARK then
            Count := Count + 1;
         end if;
      end Update;

   begin
      Iter_Unit_Subps (Unit, Update'Access);
      return Count;
   end Num_Subps_SPARK;

   ---------------
   -- Num_Units --
   ---------------

   function Num_Units return Integer is
      Count : aliased Integer := 0;

      procedure Update (U : Unit_Type);

      procedure Update (U : Unit_Type) is
         pragma Unreferenced (U);
      begin
         Count := Count + 1;
      end Update;

   --  Start of Num_Units

   begin
      Iter_Units (Update'Access);
      return Count;
   end Num_Units;

   -----------------------
   -- Reset_All_Results --
   -----------------------

   procedure Reset_All_Results is
   begin
      Unit_Map := Unit_Maps.Empty_Map;
   end Reset_All_Results;

   ---------------
   -- Subp_Name --
   ---------------

   function Subp_Name (Subp : Subp_Type) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Subp.Name);
   begin
      return S.all;
   end Subp_Name;

   ---------------
   -- Subp_File --
   ---------------

   function Subp_File (Subp : Subp_Type) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Subp.File);
   begin
      return S.all;
   end Subp_File;

   ---------------
   -- Subp_Line --
   ---------------

   function Subp_Line (Subp : Subp_Type) return Integer is (Subp.Line);

   ---------------
   -- Unit_Name --
   ---------------

   function Unit_Name (Unit : Unit_Type) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Unit);
   begin
      return S.all;
   end Unit_Name;

   -----------------------
   -- Update_Subp_Entry --
   -----------------------

   procedure Update_Subp_Entry
     (Unit    : Unit_Type;
      Subp    : Subp_Type;
      Process : not null access procedure (Stat : in out Stat_Rec))
   is

      procedure Update_Unit_Entry (U : Unit_Type; Map : in out Subp_Maps.Map);

      procedure Call_Back (S : Subp_Type; Stat : in out Stat_Rec);
      --  wrapper for the client callback

      -----------------------
      -- Update_Subp_Entry --
      -----------------------

      procedure Call_Back (S : Subp_Type; Stat : in out Stat_Rec)
      is
         pragma Unreferenced (S);
      begin
         Process (Stat);
      end Call_Back;

      -----------------------
      -- Update_Unit_Entry --
      -----------------------

      procedure Update_Unit_Entry (U : Unit_Type; Map : in out Subp_Maps.Map)
      is
         pragma Unreferenced (U);
         use Subp_Maps;

         C        : Cursor;
         Inserted : Boolean;
      begin
         Map.Insert (Subp, Default_Stat, C, Inserted);
         Map.Update_Element (C, Call_Back'Access);
      end Update_Unit_Entry;

      use Unit_Maps;
      C        : Cursor;
      Inserted : Boolean;

   --  Start of Update_Subp_Entry

   begin
      Unit_Map.Insert (Unit, Subp_Maps.Empty_Map, C, Inserted);
      Unit_Map.Update_Element (C, Update_Unit_Entry'Access);
   end Update_Subp_Entry;

end Report_Database;
