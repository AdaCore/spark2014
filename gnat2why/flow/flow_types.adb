------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           F L O W _ T Y P E S                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2014, Altran UK Limited              --
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

with Namet;             use Namet;
with Sem_Util;          use Sem_Util;
with Snames;            use Snames;

with Output;            use Output;
with Casing;            use Casing;

with Why;

with Flow_Utility;      use Flow_Utility;
with Flow_Tree_Utility; use Flow_Tree_Utility;

package body Flow_Types is

   Debug_Print_Node_Numbers : constant Boolean := False;
   --  Enable this to print the gnat node numbers alongside flow id's, so
   --  instead of "X.Y" we might print "X.Y < 2082; 2255 >". This can help
   --  debug issues where two nodes print to the same but do not compare
   --  equal. (This can happen if you forget to use Unique_Entity or
   --  Original_Record_Component.)

   use type Ada.Containers.Count_Type;

   -----------------------
   -- Flow_Id operators --
   -----------------------

   function "=" (Left, Right : Flow_Id) return Boolean is
   begin
      if Left.Kind /= Right.Kind then
         return False;
      end if;

      pragma Assert_And_Cut (Left.Kind = Right.Kind);

      case Left.Kind is
         when Null_Value =>
            return True;

         when others =>
            if Left.Variant /= Right.Variant then
               return False;
            end if;
      end case;

      pragma Assert_And_Cut (Left.Kind = Right.Kind and then
                             Left.Kind in Direct_Mapping |
                                          Record_Field |
                                          Synthetic_Null_Export |
                                          Magic_String and then
                             Left.Variant = Right.Variant);

      case Left.Kind is
         when Null_Value =>
            raise Program_Error;

         when Direct_Mapping | Record_Field =>
            if Left.Node /= Right.Node then
               return False;
            end if;
            if Left.Facet /= Right.Facet then
               return False;
            end if;

            if Left.Kind = Record_Field then
               if Left.Component.Length = Right.Component.Length then
                  for I in Natural range 1 .. Natural (Left.Component.Length)
                  loop
                     if not Same_Component (Left.Component (I),
                                            Right.Component (I))
                     then
                        return False;
                     end if;
                  end loop;
               else
                  return False;
               end if;
            end if;

            return True;

         when Magic_String =>
            return Name_Equal (Left.Name, Right.Name);

         when Synthetic_Null_Export =>
            return True;
      end case;
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
         when Synthetic_Null_Export =>
            return 1;
         when Direct_Mapping | Record_Field =>
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
      Variant : Flow_Id_Variant  := Normal_Use;
      Facet   : Variable_Facet_T := Normal_Part)
      return Flow_Id is
   begin
      return (Kind    => Direct_Mapping,
              Variant => Variant,
              Node    => N,
              Facet   => Facet);
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
      Variant : Flow_Id_Variant  := Normal_Use;
      Facet   : Variable_Facet_T := Normal_Part)
      return Flow_Id
   is
      F : Flow_Id := (Kind        => Record_Field,
                      Variant     => Variant,
                      Node        => Empty,
                      Facet       => Facet,
                      Component   => Entity_Lists.Empty_Vector);
      P : Node_Id;
   begin
      P := N;
      while Nkind (P) = N_Selected_Component loop
         F.Component.Append
           (Original_Record_Component (Entity (Selector_Name (P))));
         P := Prefix (P);
      end loop;
      F.Component.Reverse_Elements;

      case Nkind (P) is
         when N_Identifier | N_Expanded_Name =>
            --  X .Y.Z
            F.Node := Unique_Entity (Entity (P));

         when N_Attribute_Reference =>
            --  X'Old .Y.Z
            F.Node := Entity (Prefix (P));

         when others =>
            raise Why.Unexpected_Node;
      end case;

      return F;
   end Record_Field_Id;

   -------------------
   -- Add_Component --
   -------------------

   function Add_Component
     (F    : Flow_Id;
      Comp : Entity_Id)
      return Flow_Id
   is
      Tmp : Flow_Id;
   begin
      Tmp := (Kind        => Record_Field,
              Variant     => F.Variant,
              Node        => F.Node,
              Facet       => F.Facet,
              Component   => Entity_Lists.Empty_Vector);

      if F.Kind = Record_Field then
         Tmp.Component := F.Component;
      end if;
      Tmp.Component.Append (Original_Record_Component (Comp));

      return Tmp;
   end Add_Component;

   ---------------------
   -- Is_Discriminant --
   ---------------------

   function Is_Discriminant (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Record_Field =>
            if F.Facet /= Normal_Part then
               return False;
            else
               return Ekind (F.Component.Last_Element) = E_Discriminant;
            end if;
         when Direct_Mapping | Magic_String | Synthetic_Null_Export =>
            return False;
         when Null_Value =>
            raise Why.Unexpected_Node;
      end case;
   end Is_Discriminant;

   ----------------
   -- Has_Bounds --
   ----------------

   function Has_Bounds
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Boolean
   is
      T : Entity_Id;
   begin
      case F.Kind is
         when Null_Value | Synthetic_Null_Export | Magic_String =>
            return False;

         when Direct_Mapping =>
            T := Get_Full_Type (F.Node, Scope);

         when Record_Field =>
            if F.Facet /= Normal_Part then
               return False;
            else
               T := Get_Full_Type (F.Component.Last_Element, Scope);
            end if;
      end case;

      case Ekind (T) is
         when Array_Kind =>
            return not Is_Constrained (T);

         when others =>
            return False;
      end case;
   end Has_Bounds;

   -----------------
   -- Is_Volatile --
   -----------------

   function Is_Volatile (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Null_Value | Magic_String =>
            return False;
         when Direct_Mapping | Record_Field =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
               pragma Assert (Nkind (E) in N_Entity);
            begin
               case Ekind (E) is
                  when E_Abstract_State =>
                     return Is_External_State (E);
                  when Object_Kind =>
                     return Is_Effectively_Volatile (E);
                  when others =>
                     return False;
               end case;
            end;
         when Synthetic_Null_Export =>
            --  The special null export is a volatile (AR, EW).
            return True;
      end case;
   end Is_Volatile;

   -----------------------
   -- Has_Async_Readers --
   -----------------------

   function Has_Async_Readers (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Synthetic_Null_Export =>
            return True;
         when others =>
            return Is_Volatile (F) and then
              Has_Volatile_Aspect (Get_Direct_Mapping_Id (F),
                                   Pragma_Async_Readers);
      end case;
   end Has_Async_Readers;

   -----------------------
   -- Has_Async_Writers --
   -----------------------

   function Has_Async_Writers (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Synthetic_Null_Export =>
            return False;
         when others =>
            return Is_Volatile (F) and then
              Has_Volatile_Aspect (Get_Direct_Mapping_Id (F),
                                   Pragma_Async_Writers);
      end case;
   end Has_Async_Writers;

   -------------------------
   -- Has_Effective_Reads --
   -------------------------

   function Has_Effective_Reads (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Synthetic_Null_Export =>
            return False;
         when others =>
            return Is_Volatile (F) and then
              Has_Volatile_Aspect (Get_Direct_Mapping_Id (F),
                                   Pragma_Effective_Reads);
      end case;
   end Has_Effective_Reads;

   --------------------------
   -- Has_Effective_Writes --
   --------------------------

   function Has_Effective_Writes (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Synthetic_Null_Export =>
            return True;
         when others =>
            return Is_Volatile (F) and then
              Has_Volatile_Aspect (Get_Direct_Mapping_Id (F),
                                   Pragma_Effective_Writes);
      end case;
   end Has_Effective_Writes;

   -----------------------
   -- Is_Abstract_State --
   -----------------------

   function Is_Abstract_State (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping =>
            return Nkind (F.Node) in N_Entity and then
              Ekind (F.Node) = E_Abstract_State;

         when others =>
            return False;
      end case;
   end Is_Abstract_State;

   ---------------------
   -- Magic_String_Id --
   ---------------------

   function Magic_String_Id
     (S       : Entity_Name;
      Variant : Flow_Id_Variant := Normal_Use)
      return Flow_Id is
   begin
      return (Kind    => Magic_String,
              Variant => Variant,
              Name    => S);
   end Magic_String_Id;

   --------------------
   -- Change_Variant --
   --------------------

   function Change_Variant (F       : Flow_Id;
                            Variant : Flow_Id_Variant)
                            return Flow_Id
   is
   begin
      case F.Kind is
         when Null_Value =>
            return F;
         when others =>
            return F'Update (Variant => Variant);
      end case;
   end Change_Variant;

   function Change_Variant (FS      : Flow_Id_Sets.Set;
                            Variant : Flow_Id_Variant)
                            return Flow_Id_Sets.Set
   is
      New_Flow_Id_Set : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for F of FS loop
         New_Flow_Id_Set.Include (Change_Variant (F, Variant));
      end loop;

      return New_Flow_Id_Set;
   end Change_Variant;

   -------------------
   -- Parent_Record --
   -------------------

   function Parent_Record (F : Flow_Id) return Flow_Id is
   begin
      return R : Flow_Id := F do
         if R.Facet /= Normal_Part then
            R.Facet := Normal_Part;
         else
            R.Component.Delete_Last;
         end if;
         if F.Kind = Record_Field and then R.Component.Length = 0 then
            R := (Kind    => Direct_Mapping,
                  Variant => F.Variant,
                  Node    => F.Node,
                  Facet   => F.Facet);
         end if;
      end return;
   end Parent_Record;

   ---------------------
   -- Entire_Variable --
   ---------------------

   function Entire_Variable (F : Flow_Id) return Flow_Id
   is
   begin
      case F.Kind is
         when Null_Value |
              Magic_String |
              Synthetic_Null_Export =>
            return F;

         when Direct_Mapping | Record_Field =>
            return R : Flow_Id do
               R := (Kind    => Direct_Mapping,
                     Variant => F.Variant,
                     Node    => F.Node,
                     Facet   => Normal_Part);
            end return;
      end case;
   end Entire_Variable;

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
         when Synthetic_Null_Export =>
            Output.Write_Str (" (synthetic)");
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
      function Get_Unmangled_Name (N : Node_Id) return String;

      ------------------------
      -- Get_Unmangled_Name --
      ------------------------

      function Get_Unmangled_Name (N : Node_Id) return String
      is
      begin
         if Nkind (N) in N_Entity then
            if Ekind (N) in Subprogram_Kind
              and then Present (Overridden_Operation (N))
            then
               return Get_Unmangled_Name (Overridden_Operation (N));
            end if;
         end if;

         Get_Name_String (Chars (N));
         Set_Casing (Mixed_Case);
         return Name_Buffer (1 .. Name_Len);
      end Get_Unmangled_Name;

      R : Unbounded_String := Null_Unbounded_String;
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            if Nkind (F.Node) in N_Entity and then
              Ekind (F.Node) = E_Abstract_State
            then
               --  Print "Prefix.State" instead of just "State", but only
               --  for abstract state for now. (However, the code below
               --  would work for any other flow id as well.)
               case Nkind (F.Node) is
                  when N_Entity =>
                     Append (R, Get_Unmangled_Name (Scope (F.Node)));
                  when others =>
                     Append (R, Get_Unmangled_Name (Scope (Entity (F.Node))));
               end case;
               Append (R, ".");
            end if;
         when Null_Value | Magic_String | Synthetic_Null_Export =>
            null;
      end case;

      case F.Kind is
         when Null_Value =>
            Append (R, "<void>");

         when Synthetic_Null_Export =>
            Append (R, "null");

         when Direct_Mapping =>
            Append (R, Get_Unmangled_Name (F.Node));

         when Record_Field =>
            Append (R, Get_Unmangled_Name (F.Node));
            for Comp of F.Component loop
               Append (R, ".");
               Append (R, Get_Unmangled_Name (Comp));
            end loop;

         when Magic_String =>
            Append (R, F.Name.all);
      end case;

      if F.Kind in Direct_Mapping | Record_Field then
         case F.Facet is
            when Normal_Part =>
               null;

            when Private_Part =>
               Append (R, "'Private_Part");

            when Extension_Part =>
               Append (R, "'Extensions");

            when The_Tag =>
               Append (R, "'Tag");

            when The_Bounds =>
               Append (R, "'Bounds");
         end case;
      end if;

      if Debug_Print_Node_Numbers then
         if F.Kind in Direct_Mapping | Record_Field then
            Append (R, " <" & F.Node'Img);
            if F.Kind = Record_Field then
               for N of F.Component loop
                  Append (R, ";" & N'Img);
               end loop;
            end if;
            Append (R, " >");
         end if;
      end if;

      return To_String (R);
   end Flow_Id_To_String;

   -------------------------
   -- Is_Easily_Printable --
   -------------------------

   function Is_Easily_Printable (F : Flow_Id) return Boolean
   is
   begin
      case F.Kind is
         when Null_Value |
              Record_Field |
              Magic_String |
              Synthetic_Null_Export =>
            return True;

         when Direct_Mapping =>
            case Nkind (F.Node) is
               when N_Has_Chars =>
                  return True;
               when others =>
                  return False;
            end case;

      end case;
   end Is_Easily_Printable;

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

   -------------------------
   -- To_Entire_Variables --
   -------------------------

   function To_Entire_Variables (S : Flow_Id_Sets.Set)
                                 return Flow_Id_Sets.Set
   is
      R : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for X of S loop
         R.Include (Entire_Variable (X));
      end loop;
      return R;
   end To_Entire_Variables;

   -----------------
   -- To_Name_Set --
   -----------------

   function To_Name_Set (S : Flow_Id_Sets.Set) return Name_Set.Set is
      N : Name_Set.Set := Name_Set.Empty_Set;
   begin
      for X of S loop
         case X.Kind is
            when Direct_Mapping | Record_Field =>
               declare
                  E_Name : constant Entity_Name :=
                    new String'(Unique_Name (X.Node));
               begin
                  N.Include (E_Name);
               end;

            when Magic_String =>
               N.Include (X.Name);

            when Null_Value | Synthetic_Null_Export =>
               raise Program_Error;
         end case;
      end loop;
      return N;
   end To_Name_Set;

   -----------------
   -- To_Node_Set --
   -----------------

   function To_Node_Set (S : Flow_Id_Sets.Set) return Node_Sets.Set is
      N : Node_Sets.Set := Node_Sets.Empty_Set;
   begin
      for F of S loop
         pragma Assert (F.Kind = Direct_Mapping);
         N.Include (Get_Direct_Mapping_Id (F));
      end loop;
      return N;
   end To_Node_Set;

   --------------------
   -- To_Flow_Id_Set --
   --------------------

   function To_Flow_Id_Set (S : Node_Sets.Set) return Flow_Id_Sets.Set is
      FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for E of S loop
         FS.Include (Direct_Mapping_Id (E));
      end loop;
      return FS;
   end To_Flow_Id_Set;

end Flow_Types;
