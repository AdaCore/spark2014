------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           F L O W _ T Y P E S                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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

with Ada.Characters.Handling;
with Ada.Containers;                 use Ada.Containers;
with Ada.Strings.Unbounded;          use Ada.Strings.Unbounded;
with Ada.Strings;
with Errout;                         use Errout;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Utility;                   use Flow_Utility;
with GNATCOLL.Utils;
with Gnat2Why_Args;
with Hashing;                        use Hashing;
with Interfaces;
with Namet;                          use Namet;
with Output;
with Sem_Util;                       use Sem_Util;
with Snames;                         use Snames;

package body Flow_Types is

   Debug_Print_Node_Numbers : constant Boolean := False;
   --  Enable this to print the gnat node numbers alongside flow id's, so
   --  instead of "X.Y" we might print "X.Y < 2082; 2255 >". This can help
   --  debug issues where two nodes print to the same but do not compare
   --  equal. (This can happen if you forget to use Unique_Entity or
   --  Original_Record_Component.)

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
               declare
                  Left_Len : constant Ada.Containers.Count_Type :=
                    Left.Component.Length;

               begin
                  return
                    Left_Len > 0
                    and then Left_Len = Right.Component.Length
                    and then
                    (for all J in Positive range 1 .. Positive (Left_Len) =>
                       Same_Component (Left.Component (J),
                                       Right.Component (J)));
               end;
            end if;

            return True;

         when Magic_String =>
            return Left.Name = Right.Name;

         when Synthetic_Null_Export =>
            return True;
      end case;
   end "=";

   function "<" (Left, Right : Flow_Id) return Boolean is
   begin
      if Left.Kind /= Right.Kind then
         return Left.Kind < Right.Kind;
      end if;

      pragma Assert (Left.Kind = Right.Kind);

      if Left.Variant /= Right.Variant then
         return Left.Variant < Right.Variant;
      end if;

      pragma Assert (Left.Variant = Right.Variant);

      case Left.Kind is
         when Null_Value =>
            return False;

         when Direct_Mapping
            | Record_Field
            =>
            if Left.Node /= Right.Node then
               return Unique_Name (Left.Node) < Unique_Name (Right.Node);
            end if;

            pragma Assert (Left.Node = Right.Node);

            if Left.Facet /= Right.Facet then
               return Left.Facet < Right.Facet;
            end if;

            pragma Assert (Left.Facet = Right.Facet);

            if Left.Kind = Record_Field then
               declare
                  Left_Len  : constant Ada.Containers.Count_Type :=
                    Left.Component.Length;

                  Right_Len : constant Ada.Containers.Count_Type :=
                    Right.Component.Length;

               begin
                  pragma Assert (Left_Len > 0 and then Right_Len > 0);
                  if Left_Len = Right_Len then
                     for J in 1 .. Positive (Left_Len) loop
                        --  We iterate until we find two different elements and
                        --  at that point we return the result of their
                        --  comparison.
                        declare
                           Left_Comp  : constant Entity_Id :=
                             Left.Component (J);
                           Right_Comp : constant Entity_Id :=
                             Right.Component (J);

                        begin
                           if Left_Comp /= Right_Comp then
                              return Unique_Name (Left_Comp) <
                                Unique_Name (Right_Comp);
                           end if;
                        end;
                     end loop;
                     return False;
                  else
                     return Left_Len < Right_Len;
                  end if;
               end;
            end if;

            pragma Assert (Left = Right);
            return False;

         when Magic_String =>
            return To_String (Left.Name) < To_String (Right.Name);

         when Synthetic_Null_Export =>
            return False;
      end case;
   end "<";

   ----------
   -- Hash --
   ----------

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type is
   begin
      case N.Kind is
         when Null_Value =>
            return Generic_Integer_Hash (-1);
         when Synthetic_Null_Export =>
            return Generic_Integer_Hash (-2 - Flow_Id_Variant'Pos (N.Variant));
         when Direct_Mapping =>
            return Generic_Integer_Hash
              (Integer (N.Node) + Variable_Facet_T'Pos (N.Facet));
         when Record_Field =>
            declare
               use Interfaces;

               H : Unsigned_32 :=
                 Unsigned_32 (Generic_Integer_Hash (Integer (N.Node)));

               procedure Hash_Component (C : Entity_Vectors.Cursor);
               --  Update hash with a component C. Especially in debug mode
               --  this is faster than iterating over a component, because the
               --  tampering check is accessed only once for Iterate and not
               --  for each call to Element.

               --------------------
               -- Hash_Component --
               --------------------

               procedure Hash_Component (C : Entity_Vectors.Cursor) is
                  use Entity_Vectors;

               begin
                  H := Rotate_Left (H, 5);
                  H := H + Unsigned_32 (Component_Hash (Element (C))) + 1;
               end Hash_Component;

            begin
               H := H + Flow_Id_Variant'Pos (N.Variant) * 19;
               H := H + Variable_Facet_T'Pos (N.Facet) * 17;
               N.Component.Iterate (Hash_Component'Access);
               return Ada.Containers.Hash_Type (H);
            end;
         when Magic_String =>
            return Name_Hash (N.Name);
      end case;
   end Hash;

   -----------------------
   -- Direct_Mapping_Id --
   -----------------------

   function Direct_Mapping_Id
     (N       : Node_Or_Entity_Id;
      Variant : Flow_Id_Variant  := Normal_Use;
      Facet   : Variable_Facet_T := Normal_Part)
      return Flow_Id
   is
      Canonical_Node : Node_Or_Entity_Id;
   begin
      if Nkind (N) in N_Entity
        and then Ekind (N) in E_Abstract_State | Incomplete_Kind
        and then Has_Non_Limited_View (N)
      then
         Canonical_Node := Non_Limited_View (N);
      else
         Canonical_Node := N;
      end if;

      return (Kind    => Direct_Mapping,
              Variant => Variant,
              Node    => Canonical_Node,
              Facet   => Facet);
   end Direct_Mapping_Id;

   ---------------------------
   -- Get_Direct_Mapping_Id --
   ---------------------------

   function Get_Direct_Mapping_Id (F : Flow_Id) return Node_Id is (F.Node);

   ---------------------
   -- Record_Field_Id --
   ---------------------

   function Record_Field_Id
     (N       : Node_Id;
      Variant : Flow_Id_Variant  := Normal_Use;
      Facet   : Variable_Facet_T := Normal_Part)
      return Flow_Id
   is
      F : Flow_Id := (Kind      => Record_Field,
                      Variant   => Variant,
                      Node      => <>,
                      Facet     => Facet,
                      Component => Entity_Vectors.Empty_Vector);
      P : Node_Id := N;
   begin
      loop
         declare
            Selector : constant Entity_Id := Entity (Selector_Name (P));
         begin
            F.Component.Append
              (if Ekind (Selector) in E_Component | E_Discriminant
               then Original_Record_Component (Selector)
               else Selector);
         end;
         P := Prefix (P);

         exit when Nkind (P) /= N_Selected_Component;
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
            raise Program_Error;
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
      Tmp : Flow_Id :=
        (Kind      => Record_Field,
         Variant   => F.Variant,
         Node      => F.Node,
         Facet     => F.Facet,
         Component => (if F.Kind = Record_Field
                       then F.Component
                       else Entity_Vectors.Empty_Vector));

   begin
      Tmp.Component.Append
        (if Is_Part_Of_Concurrent_Object (Comp)
         then Comp
         else Original_Record_Component (Comp));

      return Tmp;
   end Add_Component;

   --------------------------------
   -- Belongs_To_Concurrent_Type --
   --------------------------------

   function Belongs_To_Concurrent_Type (F : Flow_Id) return Boolean is
   begin
      if F.Kind = Record_Field
        and then Ekind (Get_Direct_Mapping_Id (F)) in E_Protected_Type
                                                    | E_Task_Type
      then
         declare
            Comp : constant Entity_Id := F.Component.First_Element with Ghost;
         begin
            pragma Assert (Is_Part_Of_Concurrent_Object (Comp)
                             or else Is_Concurrent_Component_Or_Discr (Comp));
            return True;
         end;
      else
         return False;
      end if;
   end Belongs_To_Concurrent_Type;

   ---------------------
   -- Is_Discriminant --
   ---------------------

   function Is_Discriminant (F : Flow_Id) return Boolean is
     (F.Kind = Record_Field
      and then F.Facet = Normal_Part
      and then Ekind (F.Component.Last_Element) = E_Discriminant);

   -----------------
   -- Is_Volatile --
   -----------------

   function Is_Volatile (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Null_Value =>
            return False;

         when Magic_String =>
            return GG_Is_Volatile (F.Name);

         when Direct_Mapping | Record_Field =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);

            begin
               return (Ekind (E) in E_Abstract_State
                                  | E_Protected_Type
                                  | E_Task_Type
                                  | Object_Kind
                       and then Has_Volatile (E))
                 or else
                   (Ekind (E) in E_Task_Type | E_Protected_Type
                    and then F.Kind = Record_Field
                    and then Has_Volatile (F.Component.First_Element));
            end;

         when Synthetic_Null_Export =>
            --  The special null export is a volatile (AR, EW)
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
         when Magic_String =>
            return GG_Is_Volatile (F.Name)
              and then GG_Has_Async_Readers (F.Name);
         when others =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               return (Ekind (E) in E_Abstract_State
                                  | E_Protected_Type
                                  | E_Task_Type
                                  | Object_Kind
                 and then Has_Volatile (E)
                 and then Has_Volatile_Property (E, Pragma_Async_Readers))
                   or else
                 (Ekind (E) in E_Task_Type | E_Protected_Type
                  and then F.Kind = Record_Field
                  and then Has_Volatile (F.Component.First_Element)
                  and then Has_Volatile_Property (F.Component.First_Element,
                                                  Pragma_Async_Readers));
            end;
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
         when Magic_String =>
            return GG_Is_Volatile (F.Name)
              and then GG_Has_Async_Writers (F.Name);
         when others =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               return (Ekind (E) in E_Abstract_State
                                  | E_Protected_Type
                                  | E_Task_Type
                                  | Object_Kind
                 and then Has_Volatile (E)
                 and then Has_Volatile_Property (E, Pragma_Async_Writers))
                   or else
                 (Ekind (E) in E_Task_Type | E_Protected_Type
                  and then F.Kind = Record_Field
                  and then Has_Volatile (F.Component.First_Element)
                  and then Has_Volatile_Property (F.Component.First_Element,
                                                  Pragma_Async_Writers));
            end;
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
         when Magic_String =>
            return GG_Is_Volatile (F.Name)
              and then GG_Has_Effective_Reads (F.Name);
         when others =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               return (Ekind (E) in E_Abstract_State
                                  | E_Protected_Type
                                  | E_Task_Type
                                  | Object_Kind
                 and then Has_Volatile (E)
                 and then Has_Volatile_Property (E, Pragma_Effective_Reads))
                   or else
                 (Ekind (E) in E_Task_Type | E_Protected_Type
                  and then F.Kind = Record_Field
                  and then Has_Volatile (F.Component.First_Element)
                  and then Has_Volatile_Property (F.Component.First_Element,
                                                  Pragma_Effective_Reads));

            end;
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
         when Magic_String =>
            return GG_Is_Volatile (F.Name)
              and then GG_Has_Effective_Writes (F.Name);
         when others =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               return (Ekind (E) in E_Abstract_State
                                  | E_Protected_Type
                                  | E_Task_Type
                                  | Object_Kind
                 and then Has_Volatile (E)
                 and then Has_Volatile_Property (E, Pragma_Effective_Writes))
                   or else
                 (Ekind (E) in E_Task_Type | E_Protected_Type
                  and then F.Kind = Record_Field
                  and then Has_Volatile (F.Component.First_Element)
                  and then Has_Volatile_Property (F.Component.First_Element,
                                                  Pragma_Effective_Writes));
            end;
      end case;
   end Has_Effective_Writes;

   -----------------------
   -- Is_Abstract_State --
   -----------------------

   function Is_Abstract_State (F : Flow_Id) return Boolean
   is
     (Present (F)
      and then
        (case F.Kind is
            when Direct_Mapping => Is_Abstract_State (F.Node),
            when Magic_String   => GG_Is_Abstract_State (F.Name),
            when others         => False));

   -----------------
   -- Is_Constant --
   -----------------

   function Is_Constant (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return Is_Constant_Object (F.Node);

         --  Constants (without variable input) are filtered in phase 1 and
         --  never appear in the contracts written to the ALI file.

         when Magic_String =>
            return False;

         when Synthetic_Null_Export =>
            return False;

         when Null_Value =>
            raise Program_Error;
      end case;
   end Is_Constant;

   --------------------
   -- Is_Constituent --
   --------------------

   function Is_Constituent (F : Flow_Id) return Boolean
   is
     (case F.Kind is
         when Direct_Mapping | Record_Field => Is_Constituent (F.Node),
         when Magic_String                  => GG_Is_Constituent (F.Name),
         when others                        => False);

   -------------------------
   -- Encapsulating_State --
   -------------------------

   function Encapsulating_State (F : Flow_Id) return Flow_Id
   is
     (case F.Kind is
         when Direct_Mapping | Record_Field =>
            Direct_Mapping_Id (Encapsulating_State (F.Node), F.Variant),
         when Magic_String =>
            Magic_String_Id (GG_Encapsulating_State (F.Name), F.Variant),
         when others =>
            raise Program_Error);

   ------------------------
   -- Is_Function_Entity --
   ------------------------

   function Is_Function_Entity (F : Flow_Id) return Boolean is
     (F.Kind in Direct_Mapping | Record_Field
      and then Nkind (F.Node) in N_Entity
      and then Ekind (F.Node) = E_Function);

   -----------------
   -- Is_Internal --
   -----------------

   function Is_Internal (F : Flow_Id) return Boolean is
     (F.Kind in Direct_Mapping | Record_Field
      and then Nkind (F.Node) in N_Entity
      and then Is_Internal (F.Node));

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
            raise Program_Error;
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
      --  When we are dealing with the constituent of a concurrent object then
      --  we consider the concurrent object to be the parent record.
      if Belongs_To_Concurrent_Type (F) then
         return Flow_Id'(Kind    => Direct_Mapping,
                         Variant => F.Variant,
                         Node    => F.Node,
                         Facet   => F.Facet);
      end if;

      return R : Flow_Id := F do
         if R.Facet /= Normal_Part then
            R.Facet := Normal_Part;
         else
            R.Component.Delete_Last;
         end if;
         if F.Kind = Record_Field and then R.Component.Is_Empty then
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

   function Entire_Variable (F : Flow_Id) return Flow_Id is
   begin
      case F.Kind is
         when Magic_String | Synthetic_Null_Export =>
            return F;

         when Direct_Mapping | Record_Field =>
            return
              Flow_Id'(Kind    => Direct_Mapping,
                       Variant => F.Variant,
                       Node    => F.Node,
                       Facet   => Normal_Part);

         when Null_Value =>
            raise Program_Error;
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
      use GNATCOLL.Utils;
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
      if Gnat2Why_Args.Flow_Advanced_Debug then
         case F.Kind is
            when Direct_Mapping =>
               Output.Write_Str (" <" & Image (Natural (F.Node), 1) & ">");
            when Record_Field =>
               Output.Write_Str (" <" & Image (Natural (F.Node), 1));
               for C of F.Component loop
                  Output.Write_Str ("|" & Image (Natural (C), 1));
               end loop;
               Output.Write_Str (">");
            when others =>
               null;
         end case;
      end if;
      Output.Write_Eol;
   end Print_Flow_Id;

   -----------------------
   -- Flow_Id_To_String --
   -----------------------

   function Flow_Id_To_String
     (F      : Flow_Id;
      Pretty : Boolean := False)
      return String
   is
      function Get_Unmangled_Name (N : Node_Id) return String;

      function Pretty_Print (EN : Entity_Name) return String
      with Pre => Pretty;
      --  Pretty-print an entity name by substituting double underscores with a
      --  single dot and converting strings to mixed case, e.g. "pkg__a_state"
      --  will become "Pkg.A_State".

      ------------------------
      -- Get_Unmangled_Name --
      ------------------------

      function Get_Unmangled_Name (N : Node_Id) return String is
         Nam : Node_Id := N;
      begin
         if Nkind (N) in N_Entity then
            case Ekind (N) is
               when E_Function | E_Procedure =>
                  if Present (Overridden_Operation (N)) then
                     Nam := Overridden_Operation (N);
                  end if;

                  while Present (Homonym (Nam)) loop
                     Nam := Homonym (Nam);
                  end loop;

               when E_Task_Type | E_Protected_Type =>
                  --  For single concurrent units return the original name,
                  --  i.e. without the "tk" or "t" suffixes added by expansion.
                  if Is_Single_Concurrent_Type (N) then
                     Nam := Anonymous_Object (N);
                  end if;

               --  For references to internal formal argument in predicate
               --  function bodies use name of the predicated type.

               when E_In_Parameter =>
                  declare
                     S : constant Entity_Id := Scope (N);
                  begin
                     if Ekind (S) = E_Function
                       and then Is_Predicate_Function (S)
                     then
                        Nam := Etype (N);
                     end if;
                  end;

               when others =>
                  null;
            end case;
         end if;

         Get_Name_String (Chars (Nam));
         Adjust_Name_Case (Sloc (Nam));
         return Name_Buffer (1 .. Name_Len);
      end Get_Unmangled_Name;

      ------------------
      -- Pretty_Print --
      ------------------

      function Pretty_Print (EN : Entity_Name) return String is
         Original : constant String := Strip_Child_Prefixes (To_String (EN));

         Pretty : String (1 .. Original'Length);
         --  A placeholder for the pretty-printed string; it will be as long as
         --  the original name or shorter.

         Last : Natural := 0;
         --  Length of the pretty-printed image

         Skip       : Boolean := False;
         Capitalize : Boolean := True;
         --  Control variables for skipping a second consecutive underscore and
         --  capitalizing the first letter of a compound string.
      begin
         for J in Original'Range loop
            if Skip then
               Skip := False;
            else
               Last := Last + 1;

               if Original (J) = '_' then
                  if Original (J + 1) = '_' then
                     Pretty (Last) := '.';
                     Skip := True;
                  else
                     Pretty (Last) := '_';
                  end if;
                  Capitalize := True;
               else
                  Pretty (Last) :=
                    (if Capitalize
                     then Ada.Characters.Handling.To_Upper (Original (J))
                     else Original (J));

                  Capitalize := False;
               end if;
            end if;
         end loop;

         return Pretty (1 .. Last);
      end Pretty_Print;

      R : Unbounded_String := Null_Unbounded_String;

   --  Start of processing Flow_Id_To_String

   begin
      --  Return "Prefix.State" instead of just "State" for abstract states and
      --  "Prefix.Constituent" instead of "Constituent" for constituents whose
      --  immediate scope differs from the immediate scope of the encapsulating
      --  abstract state. (However, the code below would work for any other
      --  flow id as well.)

      if F.Kind in Direct_Mapping | Record_Field
        and then (Is_Abstract_State (F.Node)
                    or else
                  (Is_Constituent (F.Node)
                     and then
                   Scope (F.Node) /= Scope (Encapsulating_State (F.Node))))
      then
         Append (R, Get_Unmangled_Name (Scope (F.Node)));
         Append (R, ".");
      end if;

      case F.Kind is
         when Null_Value =>
            Append (R, "<void>");

         when Synthetic_Null_Export =>
            Append (R, "null");

         when Direct_Mapping =>
            Append (R, Get_Unmangled_Name (F.Node));

         when Record_Field =>
            --  For parts of concurrent units return their name as for
            --  standalone objects.

            if Is_Single_Concurrent_Type (F.Node)
              and then Is_Part_Of_Concurrent_Object (F.Component.First_Element)
            then
               Append (R, Get_Unmangled_Name (F.Component.First_Element));
            else
               Append (R, Get_Unmangled_Name (F.Node));
               for Comp of F.Component loop
                  Append (R, ".");
                  Append (R, Get_Unmangled_Name (Comp));
               end loop;
            end if;

         when Magic_String =>
            Append (R, (if Pretty
                        then Pretty_Print (F.Name)
                        else To_String (F.Name)));
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

   function Is_Easily_Printable (F : Flow_Id) return Boolean is
   begin
      case F.Kind is
         when Null_Value            |
              Record_Field          |
              Magic_String          |
              Synthetic_Null_Export =>
            return True;

         when Direct_Mapping =>
            return Nkind (F.Node) in N_Has_Chars;
      end case;
   end Is_Easily_Printable;

   ----------------------------
   -- To_Ordered_Flow_Id_Set --
   ----------------------------

   function To_Ordered_Flow_Id_Set (S : Flow_Id_Sets.Set)
                                    return Ordered_Flow_Id_Sets.Set
   is
      OS : Ordered_Flow_Id_Sets.Set := Ordered_Flow_Id_Sets.Empty_Set;
   begin
      for X of S loop
         OS.Insert (X);
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

   -------------
   -- To_Name --
   -------------

   function To_Name (F : Flow_Id) return Entity_Name is
     (case F.Kind is
         when Direct_Mapping =>
            To_Entity_Name (F.Node),

         when Magic_String =>
            F.Name,

         when others =>
            raise Program_Error);

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

   function To_Flow_Id_Set
     (S    : Node_Sets.Set;
      View : Flow_Id_Variant := Normal_Use)
      return Flow_Id_Sets.Set
   is
      FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for E of S loop
         FS.Insert (if Nkind (E) = N_Selected_Component
                    then Record_Field_Id (E, View)
                    else Direct_Mapping_Id (E, View));
      end loop;
      return FS;
   end To_Flow_Id_Set;

end Flow_Types;
