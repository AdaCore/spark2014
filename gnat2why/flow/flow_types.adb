------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           F L O W _ T Y P E S                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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
------------------------------------------------------------------------------

with Ada.Strings;
with Ada.Strings.Hash;

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Sem_Util; use Sem_Util;
with Namet;    use Namet;

with Output;   use Output;
with Casing;   use Casing;

package body Flow_Types is

   use type Ada.Containers.Count_Type;

   ---------------------------
   -- To_Ordered_Entity_Set --
   ---------------------------

   function To_Ordered_Entity_Set (S : Node_Sets.Set)
                                   return Ordered_Entity_Sets.Set
   is
      OS : Ordered_Entity_Sets.Set;
   begin
      for X of S loop
         pragma Assert (Nkind (X) in N_Entity);
         OS.Include (X);
      end loop;
      return OS;
   end To_Ordered_Entity_Set;

   -----------------------
   -- Flow_Id operators --
   -----------------------

   function "=" (Left, Right : Flow_Id) return Boolean is
   begin
      if Left.Kind = Right.Kind then
         if Left.Variant = Right.Variant then
            case Left.Kind is
               when Null_Value =>
                  return True;
               when Direct_Mapping =>
                  return Left.Node = Right.Node;
               when Record_Field =>
                  if Left.Node = Right.Node
                    and then Left.Component.Length = Right.Component.Length
                  then
                     for I in Natural
                       range 1 .. Natural (Left.Component.Length) loop
                        if Left.Component (I) /= Right.Component (I) then
                           return False;
                        end if;
                     end loop;
                     return True;
                  else
                     return False;
                  end if;
               when Magic_String =>
                  return Name_Equal (Left.Name, Right.Name);
            end case;

         elsif Left.Kind = Null_Value then
            return True;

         else
            return False;
         end if;

      else
         return False;
      end if;
   end "=";

   function "<" (Left, Right : Flow_Id) return Boolean is
   begin
      return Flow_Id_To_String (Left) < Flow_Id_To_String (Right);
   end "<";

   ----------
   -- Hash --
   ----------

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type is
   begin
      case N.Kind is
         when Null_Value =>
            return 0;
         when Direct_Mapping =>
            return Ada.Strings.Hash (Unique_Name (N.Node));
         when Record_Field =>
            --  ??? We could also hash the components in order to
            --  avoid collisions between the entire variable and each
            --  record field.
            return Ada.Strings.Hash (Unique_Name (N.Node));
         when Magic_String =>
            return Ada.Strings.Hash (N.Name.all);
      end case;
   end Hash;

   -----------------------
   -- Direct_Mapping_Id --
   -----------------------

   function Direct_Mapping_Id
     (N       : Node_Or_Entity_Id;
      Variant : Flow_Id_Variant := Normal_Use)
      return Flow_Id is
   begin
      return Flow_Id'(Kind      => Direct_Mapping,
                      Variant   => Variant,
                      Node      => N,
                      Name      => Null_Entity_Name,
                      Component => Entity_Lists.Empty_Vector);
   end Direct_Mapping_Id;

   ---------------------------
   -- Get_Direct_Mapping_Id --
   ---------------------------

   function Get_Direct_Mapping_Id (F : Flow_Id) return Node_Id is
   begin
      return F.Node;
   end Get_Direct_Mapping_Id;

   ---------------------
   -- Record_Field_Id --
   ---------------------

   function Record_Field_Id
     (N       : Node_Id;
      Variant : Flow_Id_Variant := Normal_Use)
      return Flow_Id
   is
      F : Flow_Id := Flow_Id'(Kind      => Record_Field,
                              Variant   => Variant,
                              Node      => Empty,
                              Name      => Null_Entity_Name,
                              Component => Entity_Lists.Empty_Vector);
      P : Node_Id;
   begin
      P := N;
      while Nkind (P) = N_Selected_Component loop
         F.Component.Append (Entity (Selector_Name (P)));
         P := Prefix (P);
      end loop;
      pragma Assert (Nkind (P) = N_Identifier);
      F.Node := Unique_Entity (Entity (P));
      F.Component.Reverse_Elements;
      return F;
   end Record_Field_Id;

   ---------------------
   -- Magic_String_Id --
   ---------------------

   function Magic_String_Id
     (S       : Entity_Name;
      Variant : Flow_Id_Variant := Normal_Use)
      return Flow_Id is
   begin
      return Flow_Id'(Kind      => Magic_String,
                      Variant   => Variant,
                      Node      => Empty,
                      Name      => S,
                      Component => Entity_Lists.Empty_Vector);
   end Magic_String_Id;

   --------------------
   -- Change_Variant --
   --------------------

   function Change_Variant (F       : Flow_Id;
                            Variant : Flow_Id_Variant)
                            return Flow_Id
   is
      CF : Flow_Id := F;
   begin
      case F.Kind is
         when Null_Value =>
            return Null_Flow_Id;
         when others =>
            CF.Variant := Variant;
            return CF;
      end case;
   end Change_Variant;

   -------------------
   -- Parent_Record --
   -------------------

   function Parent_Record (F : Flow_Id) return Flow_Id is
   begin
      return R : Flow_Id := F do
         R.Component.Delete_Last;
         if R.Component.Length = 0 then
            R.Kind := Direct_Mapping;
         end if;
      end return;
   end Parent_Record;

   --------------------
   -- Sprint_Flow_Id --
   --------------------

   procedure Sprint_Flow_Id (F : Flow_Id) is
   begin
      Output.Write_Str (Flow_Id_To_String (F));
   end Sprint_Flow_Id;

   -------------------
   -- Print_Flow_Id --
   -------------------

   procedure Print_Flow_Id (F : Flow_Id) is
   begin
      Sprint_Flow_Id (F);
      case F.Variant is
         when Normal_Use =>
            null;
         when Initial_Value =>
            Output.Write_Str ("'initial");
         when Final_Value =>
            Output.Write_Str ("'final");
         when Initial_Grouping =>
            Output.Write_Str ("'group'initial");
         when Final_Grouping =>
            Output.Write_Str ("'group'final");
         when In_View =>
            Output.Write_Str ("'in");
         when Out_View =>
            Output.Write_Str ("'out");
      end case;
      case F.Kind is
         when Null_Value =>
            null;
         when Direct_Mapping =>
            Output.Write_Str (" (direct)");
         when Record_Field =>
            Output.Write_Str (" (record)");
         when Magic_String =>
            Output.Write_Str (" (magic)");
      end case;
      Output.Write_Eol;
   end Print_Flow_Id;

   -----------------------
   -- Flow_Id_To_String --
   -----------------------

   function Flow_Id_To_String (F : Flow_Id) return String
   is
      R : Unbounded_String := Null_Unbounded_String;
   begin
      case F.Kind is
         when Null_Value =>
            return "<null>";

         when Direct_Mapping =>
            Get_Name_String (Chars (F.Node));
            Set_Casing (Mixed_Case);
            return Name_Buffer (1 .. Name_Len);

         when Record_Field =>
            Get_Name_String (Chars (F.Node));
            Set_Casing (Mixed_Case);
            Append (R, Name_Buffer (1 .. Name_Len));
            for Comp of F.Component loop
               Append (R, ".");
               Get_Name_String (Chars (Comp));
               Set_Casing (Mixed_Case);
               Append (R, Name_Buffer (1 .. Name_Len));
            end loop;
            return To_String (R);

         when Magic_String =>
            return F.Name.all;
      end case;
   end Flow_Id_To_String;

   ----------------------------
   -- To_Ordered_Flow_Id_Set --
   ----------------------------

   function To_Ordered_Flow_Id_Set (S : Flow_Id_Sets.Set)
                                    return Ordered_Flow_Id_Sets.Set
   is
      OS : Ordered_Flow_Id_Sets.Set;
   begin
      for X of S loop
         OS.Include (X);
      end loop;
      return OS;
   end To_Ordered_Flow_Id_Set;

end Flow_Types;
