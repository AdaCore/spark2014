------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         A S S U M P T I O N _ T Y P E S                  --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with GNATCOLL.Utils;
with Hash_Cons;

package body Assumption_Types is

   Symbol_Table : constant Symbol_Table_Access := Allocate;

   function Hash (S : Subp_Type_Rec) return Ada.Containers.Hash_Type;
   function Hash (S : Base_Sloc) return Ada.Containers.Hash_Type;
   function Hash (S : My_Sloc) return Ada.Containers.Hash_Type;

   function From_JSON (V : JSON_Array) return My_Sloc;

   function "<" (Left, Right : Symbol) return Boolean;
   function "<" (Left, Right : Base_Sloc) return Boolean;
   function "<" (Left, Right : My_Sloc) return Boolean;
   --------------------
   -- Base_Sloc_File --
   --------------------

   function Base_Sloc_File (Subp : Base_Sloc) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Subp.File);
   begin
      return S.all;
   end Base_Sloc_File;

   ---------------
   -- From_JSON --
   ---------------

   function From_JSON (V : JSON_Value) return Subp_Type is
   begin
      return
        Mk_Subp (Get (Get (V, "name")),
                 From_JSON (Get (Get (V, "sloc"))));
   end From_JSON;

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

   ----------
   -- Hash --
   ----------

   function Hash (S : Subp_Type) return Ada.Containers.Hash_Type renames
     Unique_Subps.Hash;

   function Hash (S : Unit_Type) return Ada.Containers.Hash_Type is
     (Hash (Symbol (S)));

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

   function Mk_Unit (Name : String) return Unit_Type is
      S : constant Symbol := Find (Symbol_Table, Name);
   begin
      return Unit_Type (S);
   end Mk_Unit;

   ---------------
   -- Subp_Name --
   ---------------

   function Subp_Name (Subp : Subp_Type) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Subp.Name);
   begin
      return S.all;
   end Subp_Name;

   function Subp_Sloc (Subp : Subp_Type) return My_Sloc is (Subp.Sloc);

   -------------
   -- To_JSON --
   -------------

   function To_JSON (S : Subp_Type) return JSON_Value is
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
   end To_JSON;

   ---------------
   -- Unit_Name --
   ---------------

   function Unit_Name (Unit : Unit_Type) return String is
      S : constant GNATCOLL.Utils.Cst_String_Access := Get (Unit);
   begin
      return S.all;
   end Unit_Name;

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
