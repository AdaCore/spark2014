------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         A S S U M P T I O N _ T Y P E S                  --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

with Ada.Containers.Hashed_Maps;
with Ada.Containers.Vectors;
with GNATCOLL.Utils;
with Hash_Cons;

package body Assumption_Types is

   Symbol_Table : constant Symbol_Table_Access := Allocate;

   function Hash (S : Subp_Type_Rec) return Ada.Containers.Hash_Type;
   function Hash (S : Base_Sloc) return Ada.Containers.Hash_Type;
   function Hash (S : My_Sloc) return Ada.Containers.Hash_Type;

   function To_JSON_Internal (S : Subp_Type) return JSON_Value;
   function From_JSON_Internal (V : JSON_Value) return Subp_Type;

   function From_JSON (V : JSON_Array) return My_Sloc;

   function "<" (Left, Right : Symbol) return Boolean;
   function "<" (Left, Right : Base_Sloc) return Boolean;
   function "<" (Left, Right : My_Sloc) return Boolean;

   package Subp_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Subp_Type,
      Element_Type    => Positive,
      Hash            => Hash,
      Equivalent_Keys => "=");

   package Subp_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Subp_Type,
      "="          => "=");

   Subp_Vector : Subp_Vectors.Vector;
   Subp_Map    : Subp_Maps.Map;

   --------------------
   -- Base_Sloc_File --
   --------------------

   function Base_Sloc_File (Subp : Base_Sloc) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Subp.File);
   begin
      return S.all;
   end Base_Sloc_File;

   ------------------
   -- Entity_Table --
   ------------------

   function Entity_Table return JSON_Value is
      Table : constant JSON_Value := Create_Object;
   begin
      for Index in Subp_Vector.First_Index .. Subp_Vector.Last_Index loop
         Set_Field (Table,
                    Positive'Image (Index),
                    To_JSON_Internal (Subp_Vector (Index)));
      end loop;
      return Table;
   end Entity_Table;

   ---------------
   -- From_JSON --
   ---------------

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");

   function From_JSON (V : JSON_Value) return Subp_Type is
   begin
      return Subp_Vector (Get (V));
   end From_JSON;

   ------------------------
   -- From_JSON_Internal --
   ------------------------

   function From_JSON_Internal (V : JSON_Value) return Subp_Type is
   begin
      return
        Mk_Subp (Get (Get (V, "name")),
                 From_JSON (Get (Get (V, "sloc"))));
   end From_JSON_Internal;

   function From_JSON (V : JSON_Array) return My_Sloc is
      Sloc : My_Sloc;
   begin
      for Index in 1 .. Length (V) loop
         declare
            JS_Base : constant JSON_Value := Get (V, Index);
         begin
            Sloc.Append (Mk_Base_Sloc (Get (JS_Base, "file"),
                                       Get (JS_Base, "line")));
         end;
      end loop;
      return Sloc;
   end From_JSON;

   --------------
   -- From_Key --
   --------------

   function From_Key (V : String) return Subp_Type is
   begin
      return Subp_Vector (Positive'Value (V));
   end From_Key;

   pragma Annotate (Xcov, Exempt_Off);

   ----------
   -- Hash --
   ----------

   function Hash (S : Subp_Type_Rec) return Ada.Containers.Hash_Type is
      use Ada.Containers;
   begin
      return 3 * Hash (S.Name) + 9 * Hash (S.Sloc);
   end Hash;

   function Hash (S : Base_Sloc) return Ada.Containers.Hash_Type is
      use Ada.Containers;
   begin
      return 5 * Hash (S.File) + 7 * Hash_Type (S.Line);
   end Hash;

   function Hash (S : My_Sloc) return Ada.Containers.Hash_Type is
      use Ada.Containers;
      H : Hash_Type := 0;
   begin
      for B of S loop
         H := H + 13 * Hash (B);
      end loop;
      return H;
   end Hash;

   package Unique_Subps is new
     Hash_Cons (Elt_Type    => Subp_Type_Rec,
                Access_Type => Subp_Type,
                Hash        => Hash,
                "="         => "=");

   function Hash (S : Subp_Type) return Ada.Containers.Hash_Type renames
     Unique_Subps.Hash;

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");
   function Hash (S : Unit_Type) return Ada.Containers.Hash_Type is
     (Hash (Symbol (S)));
   pragma Annotate (Xcov, Exempt_Off);

   ------------------
   -- Mk_Base_Sloc --
   ------------------

   function Mk_Base_Sloc (File : String; Line : Positive) return Base_Sloc is
   begin
      return (File => Find (Symbol_Table, File), Line => Line);
   end Mk_Base_Sloc;

   -------------
   -- Mk_Subp --
   -------------

   function Mk_Subp (Name : String; Sloc : My_Sloc) return Subp_Type is
   begin
      return
        Unique_Subps.Hash_Cons
          (Subp_Type_Rec'(Name => Find (Symbol_Table, Name),
                          Sloc => Sloc));
   end Mk_Subp;

   -------------
   -- Mk_Unit --
   -------------

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");
   function Mk_Unit (Name : String) return Unit_Type is
      S : constant Symbol := Find (Symbol_Table, Name);
   begin
      return Unit_Type (S);
   end Mk_Unit;
   pragma Annotate (Xcov, Exempt_Off);

   ------------------------
   -- Parse_Entity_Table --
   ------------------------

   procedure Parse_Entity_Table (Table : JSON_Value) is

      procedure Parse_Entry (Name : UTF8_String; Value : JSON_Value);
      --  parse a mapping of the entity table

      -----------------
      -- Parse_Entry --
      -----------------

      procedure Parse_Entry (Name : UTF8_String; Value : JSON_Value) is
         Index : constant Positive := Positive'Value (Name);
         Elt   : constant Subp_Type := From_JSON_Internal (Value);
      begin
         if Index > Subp_Vector.Last_Index then
            Subp_Vector.Set_Length (Ada.Containers.Count_Type (Index));
         end if;
         Subp_Vector.Replace_Element (Index, Elt);
         Subp_Map.Insert (Elt, Index);
      end Parse_Entry;

   --  Start of processing for Parse_Entity_Table

   begin
      Subp_Map.Clear;
      Subp_Vector.Clear;
      Map_JSON_Object (Table, Parse_Entry'Access);
   end Parse_Entity_Table;

   ---------------
   -- Subp_Name --
   ---------------

   function Subp_Name (Subp : Subp_Type) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Subp.Name);
   begin
      return S.all;
   end Subp_Name;

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");
   function Subp_Sloc (Subp : Subp_Type) return My_Sloc is (Subp.Sloc);
   pragma Annotate (Xcov, Exempt_Off);

   -------------
   -- To_JSON --
   -------------

   function To_JSON (S : Subp_Type) return JSON_Value is
      C : constant Subp_Maps.Cursor := Subp_Map.Find (S);
   begin
      if Subp_Maps.Has_Element (C) then
         return Create (Subp_Maps.Element (C));
      else
         Subp_Vector.Append (S);
         Subp_Map.Insert (S, Subp_Vector.Last_Index);
         return Create (Subp_Vector.Last_Index);
      end if;
   end To_JSON;

   ----------------------
   -- To_JSON_Internal --
   ----------------------

   function To_JSON_Internal (S : Subp_Type) return JSON_Value is
      Obj     : constant JSON_Value := Create_Object;
      JS_Sloc : JSON_Array := Empty_Array;
   begin
      Set_Field (Obj, "name", Subp_Name (S));
      for Base_Sloc of S.Sloc loop
         declare
            JS_Base : constant JSON_Value := Create_Object;
         begin
            Set_Field (JS_Base, "file", Base_Sloc_File (Base_Sloc));
            Set_Field (JS_Base, "line", Base_Sloc.Line);
            Append (JS_Sloc, JS_Base);
         end;
      end loop;
      Set_Field (Obj, "sloc", JS_Sloc);
      return Obj;
   end To_JSON_Internal;

   ------------
   -- To_Key --
   ------------

   function To_Key (S : Subp_Type) return String is
      C : constant Subp_Maps.Cursor := Subp_Map.Find (S);
   begin
      if Subp_Maps.Has_Element (C) then
         return Positive'Image (Subp_Maps.Element (C));
      else
         Subp_Vector.Append (S);
         Subp_Map.Insert (S, Subp_Vector.Last_Index);
         return Positive'Image (Subp_Vector.Last_Index);
      end if;
   end To_Key;

   ---------------
   -- Unit_Name --
   ---------------

   pragma Annotate (Xcov, Exempt_On, "Not called from gnat2why");
   function Unit_Name (Unit : Unit_Type) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Unit);
   begin
      return S.all;
   end Unit_Name;
   pragma Annotate (Xcov, Exempt_Off);

   ---------
   -- "<" --
   ---------

   function "<" (Left, Right : Base_Sloc) return Boolean is
      (if Left.File < Right.File then True
       elsif Right.File < Left.File then False
       else Left.Line < Right.Line);

   function "<" (Left, Right : My_Sloc) return Boolean is
      use Sloc_Lists;
      C1, C2 : Cursor;
   begin
      C1 := First (Left);
      C2 := First (Right);
      while Has_Element (C1) loop
         if Has_Element (C2) then
            if Element (C1) < Element (C2) then
               return True;
            elsif Element (C2) < Element (C1) then
               return False;
            else
               null;
            end if;
            Next (C2);
         else
            return False;
         end if;
         Next (C1);
      end loop;
      if Has_Element (C2) then
         return True;
      else
         return False;
      end if;
   end "<";

   function "<" (Left, Right : Subp_Type) return Boolean is
     (if Left.Name < Right.Name then True
      elsif Right.Name < Left.Name then False
      else Left.Sloc < Right.Sloc);

   function "<" (Left, Right : Symbol) return Boolean is
     (Get (Left, Empty_If_Null => True).all <
          Get (Right, Empty_If_Null => True).all);

   function "<" (Left, Right : Unit_Type) return Boolean is
     (Symbol (Left) < Symbol (Right));

end Assumption_Types;
