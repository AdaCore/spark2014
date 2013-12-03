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

with Aspects;  use Aspects;
with Einfo;    use Einfo;
with Namet;    use Namet;
with Nlists;   use Nlists;
with Sem_Util; use Sem_Util;
with Snames;   use Snames;

with Output;   use Output;
with Casing;   use Casing;

with Why;

with SPARK_Util; use SPARK_Util;

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
      pragma Assert (Nkind (P) in N_Identifier | N_Expanded_Name |
                       N_Attribute_Reference);
      if Nkind (P) in N_Identifier | N_Expanded_Name then
         F.Node := Unique_Entity (Entity (P));
         F.Component.Reverse_Elements;
      elsif Nkind (P) = N_Attribute_Reference then
         F.Node := Entity (Prefix (P));
         F.Component.Reverse_Elements;
      end if;
      return F;
   end Record_Field_Id;

   --------------------------------
   -- Get_Default_Initialization --
   --------------------------------

   function Get_Default_Initialization (F : Flow_Id) return Node_Id
   is
      function Get_Component_From_Aggregate (A : Node_Id;
                                             C : Node_Id)
                                             return Node_Id;
      --  If we have a record aggregate A like (X => Y, Z => W), this
      --  returns the value attached to component C, for example if C
      --  is Z this will return W.

      function Get_Simple_Default (E : Entity_Id) return Node_Id;
      --  Recursively look for simple default values given by
      --  Default_Value and Default_Component_Value.

      function Get_Component_From_Aggregate (A : Node_Id;
                                             C : Node_Id)
                                             return Node_Id
      is
         N : Node_Id;
      begin
         N := First (Component_Associations (A));
         while Present (N) loop
            case Nkind (N) is
               when N_Component_Association =>
                  if Entity (First (Choices (N))) = C then
                     return Expression (N);
                  end if;

               when others =>
                  raise Why.Unexpected_Node;
            end case;

            N := Next (N);
         end loop;
         raise Why.Unexpected_Node;
      end Get_Component_From_Aggregate;

      function Get_Simple_Default (E : Entity_Id) return Node_Id
      is
      begin
         if Has_Aspect (E, Aspect_Default_Value) then
            return Expression
              (Find_Aspect (E, Aspect_Default_Value));
         elsif Has_Aspect (E, Aspect_Default_Component_Value) then
            return Expression
              (Find_Aspect (E, Aspect_Default_Component_Value));
         else
            case Ekind (E) is
               when E_Array_Subtype =>
                  return Get_Simple_Default (Etype (E));

               when E_Array_Type =>
                  return Get_Simple_Default (Component_Type (E));

               when others =>
                  return Empty;
            end case;
         end if;
      end Get_Simple_Default;

      N       : Node_Id;
      Comp_Id : Positive;
   begin
      case F.Kind is
         when Direct_Mapping =>
            return Get_Simple_Default (Etype (F.Node));

         when Record_Field =>
            --  We need to find the first one with a default
            --  initialization as that would overwrite any default
            --  initialization we might find later.
            Comp_Id := 1;
            for Comp of F.Component loop
               N := Expression (Parent (Comp));
               if Present (N) then
                  --  This is a field with a default initalization.

                  --  We can try and untangle any record aggregates.
                  while Comp_Id < Positive (F.Component.Length) and
                    Nkind (N) = N_Aggregate
                  loop
                     Comp_Id := Comp_Id + 1;
                     N := Get_Component_From_Aggregate
                       (N,
                        F.Component (Comp_Id));
                  end loop;

                  return N;
               end if;

               Comp_Id := Comp_Id + 1;
            end loop;

            --  We need to check if the type itself is always
            --  initialized.
            return Get_Simple_Default (Etype (F.Component.Last_Element));

         when Magic_String =>
            return Empty;

         when Null_Value =>
            raise Why.Unexpected_Node;
      end case;
   end Get_Default_Initialization;

   ----------------------------
   -- Is_Default_Initialized --
   ----------------------------

   function Is_Default_Initialized (F : Flow_Id) return Boolean
   is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return Default_Initialization (Etype (Get_Direct_Mapping_Id (F)))
              = Full_Default_Initialization;

         when Magic_String =>
            return False;

         when Null_Value =>
            raise Why.Unexpected_Node;
      end case;
   end Is_Default_Initialized;

   -----------------
   -- Is_Volatile --
   -----------------

   function Is_Volatile (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Null_Value | Magic_String =>
            return False;
         when Direct_Mapping =>
            pragma Assert (Nkind (Get_Direct_Mapping_Id (F)) in N_Entity);
            case Ekind (Get_Direct_Mapping_Id (F)) is
               when E_Variable | E_Constant =>
                  return Is_Volatile (Get_Direct_Mapping_Id (F));
               when others =>
                  return False;
            end case;
         when Record_Field =>
            raise Why.Not_Implemented;
      end case;
   end Is_Volatile;

   -----------------------
   -- Has_Async_Readers --
   -----------------------

   function Has_Async_Readers (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Null_Value | Magic_String =>
            return False;
         when Direct_Mapping =>
            return Is_Volatile (F) and then
              Present (Get_Pragma (Get_Direct_Mapping_Id (F),
                                   Pragma_Async_Readers));
         when Record_Field =>
            raise Why.Not_Implemented;
      end case;
   end Has_Async_Readers;

   -----------------------
   -- Has_Async_Writers --
   -----------------------

   function Has_Async_Writers (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Null_Value | Magic_String =>
            return False;
         when Direct_Mapping =>
            return Is_Volatile (F) and then
              Present (Get_Pragma (Get_Direct_Mapping_Id (F),
                                   Pragma_Async_Writers));
         when Record_Field =>
            raise Why.Not_Implemented;
      end case;
   end Has_Async_Writers;

   -------------------------
   -- Has_Effective_Reads --
   -------------------------

   function Has_Effective_Reads (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Null_Value | Magic_String =>
            return False;
         when Direct_Mapping =>
            return Is_Volatile (F) and then
              Present (Get_Pragma (Get_Direct_Mapping_Id (F),
                                   Pragma_Effective_Reads));
         when Record_Field =>
            --  ??? to be implemented in M318-021
            return False;
      end case;
   end Has_Effective_Reads;

   --------------------------
   -- Has_Effective_Writes --
   --------------------------

   function Has_Effective_Writes (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Null_Value | Magic_String =>
            return False;
         when Direct_Mapping =>
            return Is_Volatile (F) and then
              Present (Get_Pragma (Get_Direct_Mapping_Id (F),
                                   Pragma_Effective_Writes));
         when Record_Field =>
            raise Why.Not_Implemented;
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

   ---------------------
   -- Entire_Variable --
   ---------------------

   function Entire_Variable (F : Flow_Id) return Flow_Id
   is
   begin
      case F.Kind is
         when Null_Value | Direct_Mapping | Magic_String =>
            return F;

         when Record_Field =>
            return R : Flow_Id := F do
               R.Kind := Direct_Mapping;
               R.Component.Clear;
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
         when Direct_Mapping | Record_Field =>
            if Nkind (F.Node) in N_Entity and then
              Ekind (F.Node) = E_Abstract_State
            then
               --  Print "Prefix.State" instead of just "State", but only
               --  for abstract state for now. (However, the code below
               --  would work for any other flow id as well.)
               case Nkind (F.Node) is
                  when N_Entity =>
                     Get_Name_String (Chars (Scope (F.Node)));
                  when others =>
                     Get_Name_String (Chars (Scope (Entity (F.Node))));
               end case;
               Set_Casing (Mixed_Case);
               Append (R, Name_Buffer (1 .. Name_Len));
               Append (R, ".");
            end if;
         when Null_Value | Magic_String =>
            null;
      end case;

      case F.Kind is
         when Null_Value =>
            Append (R, "<null>");

         when Direct_Mapping =>
            Get_Name_String (Chars (F.Node));
            Set_Casing (Mixed_Case);
            Append (R, Name_Buffer (1 .. Name_Len));

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

         when Magic_String =>
            Append (R, F.Name.all);
      end case;

      return To_String (R);
   end Flow_Id_To_String;

   -------------------------
   -- Is_Easily_Printable --
   -------------------------

   function Is_Easily_Printable (F : Flow_Id) return Boolean
   is
   begin
      case F.Kind is
         when Null_Value | Record_Field | Magic_String =>
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

            when Null_Value =>
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
      Fs : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for E of S loop
         Fs.Include (Direct_Mapping_Id (E));
      end loop;
      return Fs;
   end To_Flow_Id_Set;

end Flow_Types;
