------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                      S P A R K I F Y . S T R I N G S                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Table;

package body Sparkify.Strings is

   package Chars is new Table.Table (
     Table_Component_Type => Character,
     Table_Index_Type     => Integer,
     Table_Low_Bound      => 1,
     Table_Initial        => 10000,
     Table_Increment      => 1000,
     Table_Name           => "character container");

   Table : Chars.Table_Ptr renames Chars.Table;

   ------------------
   -- Enter_String --
   ------------------

   function Enter_String (S : String) return String_Loc is
      Len   : constant Integer := S'Length;
      F     :          Integer;
   begin

      if Len = 0 then
         return Nil_String_Loc;
      else
         Chars.Increment_Last;
         F := Chars.Last;
         Chars.Set_Last (F + Len - 1);

         Table (F .. F + Len - 1) := Chars.Table_Type (S);

         return (F, F + Len - 1);
      end if;

   end Enter_String;

   ----------------
   -- Get_String --
   ----------------

   function Get_String (SL : String_Loc) return String is
   begin

      if SL = Nil_String_Loc then
         return "";
      else
         return String (Table (SL.First .. SL.Last));
      end if;

   end Get_String;

   ----------
   -- Init --
   ----------

   procedure Init is
   begin
      Chars.Init;
   end Init;

end Sparkify.Strings;
