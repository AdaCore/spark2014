------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         A S S U M P T I O N _ T Y P E S                  --
--                                                                          --
--                                  B o d y                                 --
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

with GNATCOLL.Utils;
with Hash_Cons;

package body Assumption_Types is

   Symbol_Table : constant Symbol_Table_Access := Allocate;

   function Hash (S : Subp_Type_Rec) return Ada.Containers.Hash_Type;

   function "<" (Left, Right : Symbol) return Boolean;

   ---------------
   -- From_JSON --
   ---------------

   function From_JSON (V : JSON_Value) return Subp_Type is
   begin
      return Mk_Subp (Name => Get (Get (V, "name")),
                      File => Get (Get (V, "file")),
                      Line => Get (Get (V, "line")));
   end From_JSON;

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

   ----------
   -- Hash --
   ----------

   function Hash (S : Subp_Type) return Ada.Containers.Hash_Type is
     (Unique_Subps.Hash (S));

   function Hash (S : Unit_Type) return Ada.Containers.Hash_Type is
     (Hash (Symbol (S)));

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

   -------------
   -- To_JSON --
   -------------

   function To_JSON (S : Subp_Type) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      Set_Field (Obj, "name", Subp_Name (S));
      Set_Field (Obj, "file", Subp_File (S));
      Set_Field (Obj, "line", Subp_Line (S));
      return Obj;
   end To_JSON;

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

   ---------
   -- "<" --
   ---------

   function "<" (Left, Right : Subp_Type) return Boolean is
     (if Left.File < Right.File then True
      elsif Right.File < Left.File then False
      elsif Left.Name < Right.Name then True
      elsif Right.Name < Left.Name then False
      else Left.Line < Right.Line);

   function "<" (Left, Right : Symbol) return Boolean is
     (Get (Left, Empty_If_Null => True).all <
          Get (Right, Empty_If_Null => True).all);

   function "<" (Left, Right : Unit_Type) return Boolean is
     (Symbol (Left) < Symbol (Right));

end Assumption_Types;
