------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2011-2017, AdaCore                  --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Latin_1;             use Ada.Characters.Latin_1;
with Csets;                              use Csets;
with Errout;                             use Errout;
with Fname;                              use Fname;
with Nlists;                             use Nlists;
with Output;
with Pprint;                             use Pprint;
with Sem_Aux;                            use Sem_Aux;
with Sem_Ch12;                           use Sem_Ch12;
with Sem_Eval;                           use Sem_Eval;
with Sem_Util;                           use Sem_Util;
with SPARK_Util.Subprograms;             use SPARK_Util.Subprograms;
with SPARK_Definition;                   use SPARK_Definition;
with SPARK_Util.Types;                   use SPARK_Util.Types;
with Stand;                              use Stand;
with Stringt;                            use Stringt;

package body SPARK_Util is

   ------------------------------
   -- Extra tables on entities --
   ------------------------------

   Partial_Views : Node_Maps.Map;
   --  Map from full views of entities to their partial views, for deferred
   --  constants and private types.

   ----------------------
   -- Set_Partial_View --
   ----------------------

   procedure Set_Partial_View (E, V : Entity_Id) is
   begin
      Partial_Views.Insert (E, V);
   end Set_Partial_View;

   ------------------
   -- Partial_View --
   ------------------

   function Partial_View (E : Entity_Id) return Entity_Id
   is
      C : constant Node_Maps.Cursor := Partial_Views.Find (E);
      use Node_Maps;

   begin
      return (if Has_Element (C)
              then Element (C)
              else Empty);
   end Partial_View;

   ------------------
   -- Is_Full_View --
   ------------------

   function Is_Full_View (E : Entity_Id) return Boolean is
     (Present (Partial_View (E)));

   ---------------------
   -- Is_Partial_View --
   ---------------------

   function Is_Partial_View (E : Entity_Id) return Boolean is
     ((Is_Type (E) or else Ekind (E) = E_Constant) and then
        Present (Full_View (E)));

   Specific_Tagged_Types : Node_Maps.Map;
   --  Map from classwide types to the corresponding specific tagged type

   -------------------------
   -- Set_Specific_Tagged --
   -------------------------

   procedure Set_Specific_Tagged (E, V : Entity_Id) is
   begin
      Specific_Tagged_Types.Insert
        (E,
         (if Is_Full_View (V)
            and then Full_View_Not_In_SPARK (Partial_View (V))
          then Partial_View (V)
          else V));
   end Set_Specific_Tagged;

   function Specific_Tagged (E : Entity_Id) return Entity_Id
     renames Specific_Tagged_Types.Element;

   ---------------------------------
   -- Extra tables on expressions --
   ---------------------------------

   Dispatching_Contracts : Node_Maps.Map;
   --  Map from classwide pre- and postcondition expressions to versions of
   --  the same expressions where the type of the controlling operand is of
   --  class-wide type, and corresponding calls to primitive subprograms are
   --  dispatching calls.

   ------------------------------
   -- Set_Dispatching_Contract --
   ------------------------------

   procedure Set_Dispatching_Contract (C, D : Node_Id) is
   begin
      Dispatching_Contracts.Insert (C, D);
   end Set_Dispatching_Contract;

   --------------------------
   -- Dispatching_Contract --
   --------------------------

   function Dispatching_Contract (C : Node_Id) return Node_Id is
      Primitive : constant Node_Maps.Cursor := Dispatching_Contracts.Find (C);
      use Node_Maps;

   begin
      return (if Has_Element (Primitive)
              then Element (Primitive)
              else Empty);
   end Dispatching_Contract;

   ------------------------------------
   -- Aggregate_Is_Fully_Initialized --
   ------------------------------------

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean is

      function Matching_Component_Association
        (Component   : Entity_Id;
         Association : Node_Id) return Boolean;
      --  Return whether Association matches Component

      procedure Skip_Ancestor_And_Generated_Components
        (Component : in out Entity_Id);
      --  If Component is either a component belonging to an ancestor
      --  or a compiler generated component, skip it and all similar
      --  following components.

      ------------------------------------
      -- Matching_Component_Association --
      ------------------------------------

      function Matching_Component_Association
        (Component   : Entity_Id;
         Association : Node_Id) return Boolean
      is
         CL : constant List_Id := Choices (Association);
      begin
         pragma Assert (List_Length (CL) = 1);
         declare
            Assoc : constant Node_Id := Entity (First (CL));
         begin
            --  ??? In some cases, it is necessary to go through the
            --  Root_Record_Component to compare the component from the
            --  aggregate type (Component) and the component from the aggregate
            --  (Assoc). We don't understand why this is needed.

            return Component = Assoc
              or else
                Original_Record_Component (Component) =
              Original_Record_Component (Assoc)
              or else
                Root_Record_Component (Component) =
              Root_Record_Component (Assoc);
         end;
      end Matching_Component_Association;

      --------------------------------------------
      -- Skip_Ancestor_And_Generated_Components --
      --------------------------------------------

      procedure Skip_Ancestor_And_Generated_Components
        (Component : in out Entity_Id)
      is
         function Is_Ancestor_Component (Component : Entity_Id) return Boolean;
         --  Returns True if the component in question comes from the ancestor

         ---------------------------
         -- Is_Ancestor_Component --
         ---------------------------

         function Is_Ancestor_Component (Component : Entity_Id) return Boolean
         is
            Ancestor_Typ  : Entity_Id;
            Ancestor_Comp : Entity_Id;
         begin
            if Nkind (N) /= N_Extension_Aggregate or else
              No (Ancestor_Part (N))
            then
               return False;
            end if;

            Ancestor_Typ  := Retysp (Etype (Ancestor_Part (N)));
            Ancestor_Comp := First_Component_Or_Discriminant (Ancestor_Typ);

            while Present (Ancestor_Comp) loop
               if Component = Ancestor_Comp
                 or else Original_Record_Component (Component) =
                           Original_Record_Component (Ancestor_Comp)
                 or else Root_Record_Component (Component) =
                           Root_Record_Component (Ancestor_Comp)
               then
                  return True;
               end if;

               Ancestor_Comp := Next_Component_Or_Discriminant (Ancestor_Comp);
            end loop;

            return False;
         end Is_Ancestor_Component;

      --  Start of processing for Skip_Ancestor_And_Generated_Components

      begin
         while Present (Component)
           and then (not Comes_From_Source (Component)
                       or else Is_Ancestor_Component (Component))
         loop
            Component := Next_Component_Or_Discriminant (Component);
         end loop;
      end Skip_Ancestor_And_Generated_Components;

      Typ         : constant Entity_Id := Retysp (Etype (N));
      Assocs      : List_Id;
      Component   : Entity_Id;
      Association : Node_Id;
      Not_Init    : constant Boolean :=
        Default_Initialization (Typ) /= Full_Default_Initialization;

   --  Start of processing for Aggregate_Is_Fully_Initialized

   begin
      if Is_Record_Type (Typ) or else Is_Private_Type (Typ) then
         pragma Assert (Is_Empty_List (Expressions (N)));

         Assocs      := Component_Associations (N);
         Component   := First_Component_Or_Discriminant (Typ);
         Association := First (Assocs);

         Skip_Ancestor_And_Generated_Components (Component);

         while Present (Component) loop
            if Present (Association)
              and then Matching_Component_Association (Component, Association)
            then
               if Box_Present (Association) and then Not_Init then
                  return False;
               end if;
               Next (Association);
            else
               return False;
            end if;

            Component := Next_Component_Or_Discriminant (Component);
            Skip_Ancestor_And_Generated_Components (Component);
         end loop;

      else
         pragma Assert (Is_Array_Type (Typ) or else Is_String_Type (Typ));

         Assocs := Component_Associations (N);

         if Present (Assocs) then
            Association := First (Assocs);

            while Present (Association) loop
               if Box_Present (Association) and then Not_Init then
                  return False;
               end if;
               Next (Association);
            end loop;
         end if;
      end if;

      return True;
   end Aggregate_Is_Fully_Initialized;

   ------------
   -- Append --
   ------------

   procedure Append
     (To    : in out Node_Lists.List;
      Elmts : Node_Lists.List) is
   begin
      for E of Elmts loop
         To.Append (E);
      end loop;
   end Append;

   procedure Append
     (To    : in out Why_Node_Lists.List;
      Elmts : Why_Node_Lists.List) is
   begin
      for E of Elmts loop
         To.Append (E);
      end loop;
   end Append;

   --------------------
   -- Body_File_Name --
   --------------------

   function Body_File_Name (N : Node_Id) return String is
      CU     : Node_Id := Enclosing_Lib_Unit_Node (N);
      Switch : constant Boolean :=
        Nkind (Unit (CU)) not in N_Package_Body | N_Subprogram_Body;

   begin
      if Switch and then Present (Library_Unit (CU)) then
         CU := Library_Unit (CU);
      end if;

      return File_Name (Sloc (CU));
   end Body_File_Name;

   -----------------------------------
   -- Char_To_String_Representation --
   -----------------------------------

   function Char_To_String_Representation (C : Character) return String is
   begin
      case C is

      --  Graphic characters are printed directly

      when Graphic_Character =>
         return String'(1 => C);

      --  Other characters are printed as their enumeration name in the
      --  Character enumeration in GNAT. Character'Image is not usable to get
      --  the names as it returns the character itself instead of a name for C
      --  greater than 160.

      when NUL                         => return "NUL";
      when SOH                         => return "SOH";
      when STX                         => return "STX";
      when ETX                         => return "ETX";
      when EOT                         => return "EOT";
      when ENQ                         => return "ENQ";
      when ACK                         => return "ACK";
      when BEL                         => return "BEL";
      when BS                          => return "BS";
      when HT                          => return "HT";
      when LF                          => return "LF";
      when VT                          => return "VT";
      when FF                          => return "FF";
      when CR                          => return "CR";
      when SO                          => return "SO";
      when SI                          => return "SI";

      when DLE                         => return "DLE";
      when DC1                         => return "DC1";
      when DC2                         => return "DC2";
      when DC3                         => return "DC3";
      when DC4                         => return "DC4";
      when NAK                         => return "NAK";
      when SYN                         => return "SYN";
      when ETB                         => return "ETB";
      when CAN                         => return "CAN";
      when EM                          => return "EM";
      when SUB                         => return "SUB";
      when ESC                         => return "ESC";
      when FS                          => return "FS";
      when GS                          => return "GS";
      when RS                          => return "RS";
      when US                          => return "US";

      when DEL                         => return "DEL";
      when Reserved_128                => return "Reserved_128";
      when Reserved_129                => return "Reserved_129";
      when BPH                         => return "BPH";
      when NBH                         => return "NBH";
      when Reserved_132                => return "Reserved_132";
      when NEL                         => return "NEL";
      when SSA                         => return "SSA";
      when ESA                         => return "ESA";
      when HTS                         => return "HTS";
      when HTJ                         => return "HTJ";
      when VTS                         => return "VTS";
      when PLD                         => return "PLD";
      when PLU                         => return "PLU";
      when RI                          => return "RI";
      when SS2                         => return "SS2";
      when SS3                         => return "SS3";

      when DCS                         => return "DCS";
      when PU1                         => return "PU1";
      when PU2                         => return "PU2";
      when STS                         => return "STS";
      when CCH                         => return "CCH";
      when MW                          => return "MW";
      when SPA                         => return "SPA";
      when EPA                         => return "EPA";

      when SOS                         => return "SOS";
      when Reserved_153                => return "Reserved_153";
      when SCI                         => return "SCI";
      when CSI                         => return "CSI";
      when ST                          => return "ST";
      when OSC                         => return "OSC";
      when PM                          => return "PM";
      when APC                         => return "APC";

      when No_Break_Space              => return "No_Break_Space";
      when Inverted_Exclamation        => return "Inverted_Exclamation";
      when Cent_Sign                   => return "Cent_Sign";
      when Pound_Sign                  => return "Pound_Sign";
      when Currency_Sign               => return "Currency_Sign";
      when Yen_Sign                    => return "Yen_Sign";
      when Broken_Bar                  => return "Broken_Bar";
      when Section_Sign                => return "Section_Sign";
      when Diaeresis                   => return "Diaeresis";
      when Copyright_Sign              => return "Copyright_Sign";
      when Feminine_Ordinal_Indicator  => return "Feminine_Ordinal_Indicator";
      when Left_Angle_Quotation        => return "Left_Angle_Quotation";
      when Not_Sign                    => return "Not_Sign";
      when Soft_Hyphen                 => return "Soft_Hyphen";
      when Registered_Trade_Mark_Sign  => return "Registered_Trade_Mark_Sign";
      when Macron                      => return "Macron";
      when Degree_Sign                 => return "Degree_Sign";
      when Plus_Minus_Sign             => return "Plus_Minus_Sign";
      when Superscript_Two             => return "Superscript_Two";
      when Superscript_Three           => return "Superscript_Three";
      when Acute                       => return "Acute";
      when Micro_Sign                  => return "Micro_Sign";
      when Pilcrow_Sign                => return "Pilcrow_Sign";
      when Middle_Dot                  => return "Middle_Dot";
      when Cedilla                     => return "Cedilla";
      when Superscript_One             => return "Superscript_One";
      when Masculine_Ordinal_Indicator => return "Masculine_Ordinal_Indicator";
      when Right_Angle_Quotation       => return "Right_Angle_Quotation";
      when Fraction_One_Quarter        => return "Fraction_One_Quarter";
      when Fraction_One_Half           => return "Fraction_One_Half";
      when Fraction_Three_Quarters     => return "Fraction_Three_Quarters";
      when Inverted_Question           => return "Inverted_Question";

      when UC_A_Grave                  => return "UC_A_Grave";
      when UC_A_Acute                  => return "UC_A_Acute";
      when UC_A_Circumflex             => return "UC_A_Circumflex";
      when UC_A_Tilde                  => return "UC_A_Tilde";
      when UC_A_Diaeresis              => return "UC_A_Diaeresis";
      when UC_A_Ring                   => return "UC_A_Ring";
      when UC_AE_Diphthong             => return "UC_AE_Diphthong";
      when UC_C_Cedilla                => return "UC_C_Cedilla";
      when UC_E_Grave                  => return "UC_E_Grave";
      when UC_E_Acute                  => return "UC_E_Acute";
      when UC_E_Circumflex             => return "UC_E_Circumflex";
      when UC_E_Diaeresis              => return "UC_E_Diaeresis";
      when UC_I_Grave                  => return "UC_I_Grave";
      when UC_I_Acute                  => return "UC_I_Acute";
      when UC_I_Circumflex             => return "UC_I_Circumflex";
      when UC_I_Diaeresis              => return "UC_I_Diaeresis";
      when UC_Icelandic_Eth            => return "UC_Icelandic_Eth";
      when UC_N_Tilde                  => return "UC_N_Tilde";
      when UC_O_Grave                  => return "UC_O_Grave";
      when UC_O_Acute                  => return "UC_O_Acute";
      when UC_O_Circumflex             => return "UC_O_Circumflex";
      when UC_O_Tilde                  => return "UC_O_Tilde";
      when UC_O_Diaeresis              => return "UC_O_Diaeresis";

      when Multiplication_Sign         => return "Multiplication_Sign";

      when UC_O_Oblique_Stroke         => return "UC_O_Oblique_Stroke";
      when UC_U_Grave                  => return "UC_U_Grave";
      when UC_U_Acute                  => return "UC_U_Acute";
      when UC_U_Circumflex             => return "UC_U_Circumflex";
      when UC_U_Diaeresis              => return "UC_U_Diaeresis";
      when UC_Y_Acute                  => return "UC_Y_Acute";
      when UC_Icelandic_Thorn          => return "UC_Icelandic_Thorn";

      when LC_German_Sharp_S           => return "LC_German_Sharp_S";
      when LC_A_Grave                  => return "LC_A_Grave";
      when LC_A_Acute                  => return "LC_A_Acute";
      when LC_A_Circumflex             => return "LC_A_Circumflex";
      when LC_A_Tilde                  => return "LC_A_Tilde";
      when LC_A_Diaeresis              => return "LC_A_Diaeresis";
      when LC_A_Ring                   => return "LC_A_Ring";
      when LC_AE_Diphthong             => return "LC_AE_Diphthong";
      when LC_C_Cedilla                => return "LC_C_Cedilla";
      when LC_E_Grave                  => return "LC_E_Grave";
      when LC_E_Acute                  => return "LC_E_Acute";
      when LC_E_Circumflex             => return "LC_E_Circumflex";
      when LC_E_Diaeresis              => return "LC_E_Diaeresis";
      when LC_I_Grave                  => return "LC_I_Grave";
      when LC_I_Acute                  => return "LC_I_Acute";
      when LC_I_Circumflex             => return "LC_I_Circumflex";
      when LC_I_Diaeresis              => return "LC_I_Diaeresis";
      when LC_Icelandic_Eth            => return "LC_Icelandic_Eth";
      when LC_N_Tilde                  => return "LC_N_Tilde";
      when LC_O_Grave                  => return "LC_O_Grave";
      when LC_O_Acute                  => return "LC_O_Acute";
      when LC_O_Circumflex             => return "LC_O_Circumflex";
      when LC_O_Tilde                  => return "LC_O_Tilde";
      when LC_O_Diaeresis              => return "LC_O_Diaeresis";

      when Division_Sign               => return "Division_Sign";

      when LC_O_Oblique_Stroke         => return "LC_O_Oblique_Stroke";
      when LC_U_Grave                  => return "LC_U_Grave";
      when LC_U_Acute                  => return "LC_U_Acute";
      when LC_U_Circumflex             => return "LC_U_Circumflex";
      when LC_U_Diaeresis              => return "LC_U_Diaeresis";
      when LC_Y_Acute                  => return "LC_Y_Acute";
      when LC_Icelandic_Thorn          => return "LC_Icelandic_Thorn";
      when LC_Y_Diaeresis              => return "LC_Y_Diaeresis";
      end case;
   end Char_To_String_Representation;

   -----------------------------------
   -- Component_Is_Visible_In_SPARK --
   -----------------------------------

   function Component_Is_Visible_In_SPARK (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Scope (E);

   begin
      if Ekind (E) = E_Discriminant then
         return True;

      --  Components of a concurrent type are visible except if the type full
      --  view is not in SPARK.

      elsif Is_Concurrent_Type (Ty) then

         return not Full_View_Not_In_SPARK (Ty);

      --  If the type itself is private, no components can be visible in it.
      --  This case has to be handled specifically to prevent visible
      --  components of hidden ancestors from leaking in.

      elsif not Entity_In_SPARK (Ty)
        or else (Full_View_Not_In_SPARK (Ty)
                 and then Get_First_Ancestor_In_SPARK (Ty) = Ty)
      then

         return False;

      --  Find the first record type in the hierarchy in which the field is
      --  present and see if it is in SPARK.

      else

         declare
            Orig_Comp : constant Entity_Id := Original_Record_Component (E);
            Orig_Rec  : constant Entity_Id := Scope (Orig_Comp);
            Pview_Rec : constant Entity_Id :=
              (if Present (Full_View (Orig_Rec))
               then Full_View (Orig_Rec)
               else Orig_Rec);
         begin
            return Entity_In_SPARK (Pview_Rec);
         end;
      end if;
   end Component_Is_Visible_In_SPARK;

   -------------------------------
   -- Enclosing_Concurrent_Type --
   -------------------------------

   function Enclosing_Concurrent_Type (E : Entity_Id) return Entity_Id is
     (if Is_Part_Of_Concurrent_Object (E)
      then Etype (Encapsulating_State (E))
      else Scope (E));

   --------------------
   -- Enclosing_Unit --
   --------------------

   function Enclosing_Unit (E : Entity_Id) return Entity_Id is
      S : Entity_Id;

   begin
      --  Go to unique entity to avoid bodies

      S := Unique_Entity (Scope (E));

      while Present (S) loop
         if Ekind (S) in E_Function | E_Entry | E_Procedure | E_Package
           | E_Protected_Type | E_Task_Type
         then
            --  We have found the enclosing unit, return it

            return S;
         else
            --  Go to the next scope

            S := Unique_Entity (Scope (S));
         end if;
      end loop;

      return Empty;
   end Enclosing_Unit;

   ------------------------------
   -- File_Name_Without_Suffix --
   ------------------------------

   function File_Name_Without_Suffix (File_Name : String) return String is
      Name_Index : Natural := File_Name'Last;

   begin
      pragma Assert (File_Name'Length > 0);

      --  We loop in reverse to ensure that file names that follow nonstandard
      --  naming conventions that include additional dots are handled properly,
      --  preserving dots in front of the main file suffix (for example,
      --  main.2.ada => main.2).

      while Name_Index >= File_Name'First
        and then File_Name (Name_Index) /= '.'
      loop
         Name_Index := Name_Index - 1;
      end loop;

      --  Return the part of the file name up to but not including the last dot
      --  in the name, or return the whole name as is if no dot character was
      --  found.

      if Name_Index >= File_Name'First then
         return File_Name (File_Name'First .. Name_Index - 1);

      else
         return File_Name;
      end if;
   end File_Name_Without_Suffix;

   ---------------------
   -- Full_Entry_Name --
   ---------------------

   function Full_Entry_Name (N : Node_Id) return String is

      function This_Name (N : Node_Id) return String;

      ---------------
      -- This_Name --
      ---------------

      function This_Name (N : Node_Id) return String is
      begin
         return Get_Name_String (Chars (N));
      end This_Name;

   --  Start of processing for Full_Entry_Name

   begin
      case Nkind (N) is
         when N_Selected_Component
            | N_Expanded_Name
         =>
            return Full_Entry_Name (Prefix (N)) &
              "__" & This_Name (Selector_Name (N));

         when N_Indexed_Component =>
            return Full_Entry_Name (Prefix (N));

         when N_Identifier =>
            if Scope (Entity (N)) = Standard_Standard then
               return This_Name (N);
            else
               return Full_Entry_Name (Scope (Entity (N))) &
                 "__" & This_Name (N);
            end if;

         when N_Defining_Identifier =>
            return This_Name (N);

         when others =>
            raise Program_Error;
      end case;
   end Full_Entry_Name;

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (E : Entity_Id) return String is
   begin
      --  In a few special cases, return a predefined name. These cases should
      --  match those for which Full_Name_Is_Not_Unique_Name returns True.

      if Full_Name_Is_Not_Unique_Name (E) then
         if Is_Standard_Boolean_Type (E) then
            return "bool";
         elsif E = Universal_Fixed then
            return "real";
         else
            raise Program_Error;
         end if;

      --  In the general case, return the same name as Unique_Name

      else
         return Unique_Name (E);
      end if;
   end Full_Name;

   ----------------------------------
   -- Full_Name_Is_Not_Unique_Name --
   ----------------------------------

   function Full_Name_Is_Not_Unique_Name (E : Entity_Id) return Boolean is
     (Is_Standard_Boolean_Type (E) or else E = Universal_Fixed);

   ----------------------
   -- Full_Source_Name --
   ----------------------

   function Full_Source_Name (E : Entity_Id) return String is

      function Get_Scoped_Name (E : Entity_Id) return String;
      --  Return the name of E prefixed by all the names of the scopes to which
      --  E belongs, except for Standard.

      ---------------------
      -- Get_Scoped_Name --
      ---------------------

      function Get_Scoped_Name (E : Entity_Id) return String is
         Name : constant String := Source_Name (E);
      begin
         if Has_Fully_Qualified_Name (E)
           or else Scope (E) = Standard_Standard
         then
            return Name;
         else
            return Get_Scoped_Name (Scope (E)) & "." & Name;
         end if;
      end Get_Scoped_Name;

   --  Start of processing for Full_Source_Name

   begin
      if E = Standard_Standard then
         return Get_Name_String (Name_Standard);

      elsif Scope (E) = Standard_Standard
        and then Ekind (E) not in E_Package | Subprogram_Kind
      then
         return Get_Name_String (Name_Standard) & "." &
           Get_Name_String (Chars (E));

      elsif Ekind (E) = E_Enumeration_Literal then
         return Unique_Name (Etype (E)) & "." & Get_Name_String (Chars (E));

      else
         --  Names of E_Subprogram_Body or E_Package_Body entities are not
         --  reliable, as they may not include the overloading suffix. Instead,
         --  get the name of the corresponding Unique_Entity. This is only
         --  needed here, because Scope always returns the unique entity.

         return Get_Scoped_Name (Unique_Entity (E));
      end if;
   end Full_Source_Name;

   -----------------------
   -- Get_Called_Entity --
   -----------------------

   function Get_Called_Entity (N : Node_Id) return Entity_Id is
      Nam : constant Node_Id := Name (N);

   begin
      return
        Entity (case Nkind (Nam) is
                   when N_Selected_Component => Selector_Name (Nam),
                   when N_Indexed_Component  => Selector_Name (Prefix (Nam)),
                   when others               => Nam);
   end Get_Called_Entity;

   ---------------------------------------------
   -- Get_Flat_Statement_And_Declaration_List --
   ---------------------------------------------

   function Get_Flat_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List
   is
      Cur_Stmt   : Node_Id := Nlists.First (Stmts);
      Flat_Stmts : Node_Lists.List;

   begin
      while Present (Cur_Stmt) loop
         case Nkind (Cur_Stmt) is
            when N_Block_Statement =>
               if Present (Declarations (Cur_Stmt)) then
                  Append (Flat_Stmts,
                          Get_Flat_Statement_And_Declaration_List
                            (Declarations (Cur_Stmt)));
               end if;

               Append (Flat_Stmts,
                       Get_Flat_Statement_And_Declaration_List
                         (Statements (Handled_Statement_Sequence (Cur_Stmt))));

            when others =>
               Flat_Stmts.Append (Cur_Stmt);
         end case;

         Nlists.Next (Cur_Stmt);
      end loop;

      return Flat_Stmts;
   end Get_Flat_Statement_And_Declaration_List;

   ---------------------------------
   -- Get_Formal_Type_From_Actual --
   ---------------------------------

   function Get_Formal_From_Actual (Actual : Node_Id) return Entity_Id is
      Formal : Entity_Id;

      procedure Check_Call_Param
        (Some_Formal : Entity_Id;
         Some_Actual : Node_Id);
      --  If Some_Actual is the desired actual parameter, set Formal_Type to
      --  the type of the corresponding formal parameter.

      ----------------------
      -- Check_Call_Param --
      ----------------------

      procedure Check_Call_Param
        (Some_Formal : Entity_Id;
         Some_Actual : Node_Id) is
      begin
         if Some_Actual = Actual then
            Formal := Some_Formal;
         end if;
      end Check_Call_Param;

      procedure Find_Expr_In_Call_Params is new
        Iterate_Call_Parameters (Check_Call_Param);

      Act_Par      : constant Node_Id := Parent (Actual);
      Real_Act_Par : constant Node_Id :=
        (if Nkind (Act_Par) = N_Unchecked_Type_Conversion
           and then Comes_From_Source (Act_Par)
         then Original_Node (Act_Par) else Act_Par);
      --  N_Unchecked_Type_Conversion coming from source are handled using
      --  their original node.

   --  Start of processing for Get_Formal_From_Actual

   begin
      Find_Expr_In_Call_Params
        (if Nkind (Real_Act_Par) = N_Parameter_Association
         then Parent (Real_Act_Par)
         else Real_Act_Par);

      return Formal;
   end Get_Formal_From_Actual;

   ---------------
   -- Get_Range --
   ---------------

   function Get_Range (N : Node_Id) return Node_Id is
   begin
      case Nkind (N) is
         when N_Range
            | N_Real_Range_Specification
            | N_Signed_Integer_Type_Definition
            | N_Modular_Type_Definition
            | N_Floating_Point_Definition
            | N_Ordinary_Fixed_Point_Definition
            | N_Decimal_Fixed_Point_Definition
         =>
            return N;

         when N_Subtype_Indication =>
            return Range_Expression (Constraint (N));

         when N_Identifier
            | N_Expanded_Name
         =>
            return Get_Range (Entity (N));

         when N_Defining_Identifier =>
            return
              Get_Range
                (Scalar_Range
                   (case Ekind (N) is
                    when Scalar_Kind => N,
                    when Object_Kind => Etype (N),
                    when others      => raise Program_Error));

         when others =>
            raise Program_Error;
      end case;
   end Get_Range;

   ------------------
   -- Has_Volatile --
   ------------------

   function Has_Volatile (E : Checked_Entity_Id) return Boolean is
     (if Ekind (E) = E_Abstract_State then
        Is_External_State (E)
      elsif Ekind (E) in Object_Kind then
        Is_Effectively_Volatile (E)
      else
        Is_Effectively_Volatile_Object (E));

   -------------------------
   -- Has_Volatile_Flavor --
   -------------------------

   function Has_Volatile_Flavor (E : Checked_Entity_Id;
                                 A : Volatile_Pragma_Id)
                                 return Boolean
   is
   begin
      --  Tasks are considered to have Async_Readers and Async_Writers
      if Ekind (Etype (E)) in Task_Kind then
         return A in Pragma_Async_Readers | Pragma_Async_Writers;
      end if;

      --  ??? how about arrays and records with protected or task components?

      --  Q: Why restrict the flavors of volatility for IN and OUT
      --  parameters???
      --
      --  A: See SRM 7.1.3. In short when passing a volatile through a
      --  parameter we present a 'worst case but sane' view of the volatile,
      --  which means there should be no information hiding possible and no
      --  silent side effects, so...

      case Ekind (E) is
         when E_Abstract_State | E_Variable =>
            return
              (case A is
               when Pragma_Async_Readers    => Async_Readers_Enabled (E),
               when Pragma_Async_Writers    => Async_Writers_Enabled (E),
               when Pragma_Effective_Reads  => Effective_Reads_Enabled (E),
               when Pragma_Effective_Writes => Effective_Writes_Enabled (E));

         when E_In_Parameter  =>
            --  All volatile in parameters have only async_writers set. In
            --  particular reads cannot be effective and the absence of AR is
            --  irrelevant since we are not allowed to write to it anyway.
            return A = Pragma_Async_Writers;

         when E_Out_Parameter =>
            --  Out parameters we assume that writes are effective (worst
            --  case). We do not assume reads are effective because (a - it may
            --  be illegal to read anyway, b - we ban passing a fully volatile
            --  object as an argument to an out parameter).
            return A in Pragma_Async_Readers | Pragma_Effective_Writes;

         when E_In_Out_Parameter =>
            --  For in out we just assume the absolute worst case (fully
            --  volatile).
            return True;

         when others =>
            raise Program_Error;
      end case;
   end Has_Volatile_Flavor;

   ------------------
   -- In_Main_Unit --
   ------------------

   function In_Main_Unit (E : Entity_Id) return Boolean is
      Real_Node : constant Node_Id :=
        (if Is_Itype (E)
         then Associated_Node_For_Itype (E)
         else E);

      CU : constant Node_Id := Enclosing_Lib_Unit_Node (Real_Node);

   begin
      return Unique_Defining_Entity (Unit (CU)) = Main_Unit_Entity;
   end In_Main_Unit;

   ---------------
   -- Is_Action --
   ---------------

   function Is_Action (N : Node_Id) return Boolean
   is
      L : constant List_Id := List_Containing (N);
      P : constant Node_Id := Parent (N);
   begin
      if No (L) or else No (P) then
         return False;
      end if;

      return
        (case Nkind (P) is
            when N_Component_Association =>
               L = Loop_Actions (P),
            when N_And_Then | N_Or_Else =>
               L = Actions (P),
            when N_If_Expression =>
               L = Then_Actions (P) or else L = Else_Actions (P),
            when N_Case_Expression_Alternative =>
               L = Actions (P),
            when N_Elsif_Part =>
               L = Condition_Actions (P),
            when N_Iteration_Scheme =>
               L = Condition_Actions (P),
            when N_Block_Statement =>
               L = Cleanup_Actions (P),
            when N_Expression_With_Actions =>
               L = Actions (P),
            when N_Freeze_Entity =>
               L = Actions (P),
            when others =>
               False);
   end Is_Action;

   -----------------------------------
   -- Is_Constant_After_Elaboration --
   -----------------------------------

   function Is_Constant_After_Elaboration (E : Entity_Id) return Boolean is
      Prag : constant Node_Id :=
        Get_Pragma (E, Pragma_Constant_After_Elaboration);
   begin
      if Present (Prag) then
         declare
            PAA : constant List_Id := Pragma_Argument_Associations (Prag);
         begin
            --  The pragma has an optional Boolean expression. The related
            --  property is enabled only when the expression evaluates to True.
            if Present (PAA) then
               declare
                  Expr : constant Node_Id := Expression (First (PAA));
               begin
                  return Is_True (Expr_Value (Get_Pragma_Arg (Expr)));
               end;

            --  The lack of expression means the property is enabled

            else
               return True;
            end if;
         end;

      --  No pragma means not constant after elaboration

      else
         return False;
      end if;
   end Is_Constant_After_Elaboration;

   ------------------------------------------
   -- Is_Converted_Actual_Output_Parameter --
   ------------------------------------------

   function Is_Converted_Actual_Output_Parameter (N : Node_Id) return Boolean
   is
      Formal : Entity_Id;
      Call   : Node_Id;
      Conv   : Node_Id;

   begin
      --  Find the most enclosing type conversion node

      Conv := N;
      while Nkind (Parent (Conv)) = N_Type_Conversion loop
         Conv := Parent (Conv);
      end loop;

      --  Check if this node is an out or in out actual parameter

      Find_Actual (Conv, Formal, Call);
      return Present (Formal)
        and then Ekind (Formal) in E_Out_Parameter | E_In_Out_Parameter;
   end Is_Converted_Actual_Output_Parameter;

   ---------------------------------------
   -- Is_Call_Arg_To_Predicate_Function --
   ---------------------------------------

   function Is_Call_Arg_To_Predicate_Function (N : Node_Id) return Boolean is
     (Present (N)
        and then Present (Parent (N))
        and then Nkind (Parent (N)) = N_Type_Conversion
        and then Present (Parent (Parent (N)))
        and then Is_Predicate_Function_Call (Parent (Parent (N))));

   -------------------------------------
   -- Is_Concurrent_Component_Or_Discr --
   -------------------------------------

   function Is_Concurrent_Component_Or_Discr (E : Entity_Id) return Boolean is
   begin
      --  Protected discriminants appear either as E_In_Parameter (in spec of
      --  protected types, e.g. in pragma Priority) or as E_Discriminant
      --  (everywhere else).
      return Ekind (E) in E_Component | E_Discriminant | E_In_Parameter
        and then Ekind (Scope (E)) in E_Protected_Type | E_Task_Type;
   end Is_Concurrent_Component_Or_Discr;

   -------------------------
   -- Is_Declared_In_Unit --
   -------------------------

   --  Parameters of subprograms cannot be local to a unit.

   function Is_Declared_In_Unit
     (E     : Entity_Id;
      Scope : Entity_Id) return Boolean
   is
     (Enclosing_Unit (E) = Scope and then not Is_Formal (E));

   -----------------------------
   -- Is_Ignored_Pragma_Check --
   -----------------------------

   function Is_Ignored_Pragma_Check (N : Node_Id) return Boolean is
   begin
      return Is_Pragma_Check (N, Name_Precondition)
               or else
             Is_Pragma_Check (N, Name_Pre)
               or else
             Is_Pragma_Check (N, Name_Postcondition)
               or else
             Is_Pragma_Check (N, Name_Post)
               or else
             Is_Pragma_Check (N, Name_Refined_Post)
               or else
             Is_Pragma_Check (N, Name_Static_Predicate)
               or else
             Is_Pragma_Check (N, Name_Predicate)
               or else
             Is_Pragma_Check (N, Name_Dynamic_Predicate);
   end Is_Ignored_Pragma_Check;

   --------------------------
   -- Is_In_Analyzed_Files --
   --------------------------

   function Is_In_Analyzed_Files (E : Entity_Id) return Boolean is
      Real_Entity : constant Node_Id :=
        (if Is_Itype (E)
         then Associated_Node_For_Itype (E)
         else E);

      Encl_Unit : constant Node_Id := Enclosing_Lib_Unit_Node (Real_Entity);
      --  The library unit containing E

      Main_Unit_Node : constant Node_Id := Cunit (Main_Unit);

   begin
      --  Check if the entity is either in the spec or in the body of the
      --  current compilation unit. gnat2why is now only called on requested
      --  files, so otherwise just return False.

      return Encl_Unit in Main_Unit_Node | Library_Unit (Main_Unit_Node);
   end Is_In_Analyzed_Files;

   ----------------------
   -- In_Internal_Unit --
   ----------------------

   function In_Internal_Unit (N : Node_Or_Entity_Id) return Boolean is
     (In_Internal_Unit (Sloc (N)));

   function In_Internal_Unit (S : Source_Ptr) return Boolean is
      Unit : constant Unit_Number_Type := Get_Source_Unit (S);
      File : constant File_Name_Type   := Unit_File_Name (Unit);
   begin
      return Is_Internal_File_Name (File);
   end In_Internal_Unit;

   ----------------------
   -- Is_Others_Choice --
   ----------------------

   function Is_Others_Choice (Choices : List_Id) return Boolean is
   begin
      return List_Length (Choices) = 1
        and then Nkind (First (Choices)) = N_Others_Choice;
   end Is_Others_Choice;

   ----------------------
   -- Is_Package_State --
   ----------------------

   function Is_Package_State (E : Entity_Id) return Boolean is
     (Ekind (E) = E_Abstract_State
        or else
      (Ekind (E) = E_Variable and then Ekind (Scope (E)) = E_Package));

   ---------------
   -- Is_Pragma --
   ---------------

   function Is_Pragma (N : Node_Id; Name : Pragma_Id) return Boolean is
     (Nkind (N) = N_Pragma
        and then Get_Pragma_Id (Pragma_Name (N)) = Name);

   ----------------------------------
   -- Is_Pragma_Annotate_Gnatprove --
   ----------------------------------

   function Is_Pragma_Annotate_GNATprove (N : Node_Id) return Boolean is
     (Is_Pragma (N, Pragma_Annotate)
        and then
      Get_Name_String
        (Chars (Get_Pragma_Arg (First (Pragma_Argument_Associations (N)))))
      = "gnatprove");

   ------------------------------
   -- Is_Pragma_Assert_And_Cut --
   ------------------------------

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean is
      Orig : constant Node_Id := Original_Node (N);

   begin
      return
        (Present (Orig)
           and then Is_Pragma (Orig, Pragma_Assert_And_Cut));
   end Is_Pragma_Assert_And_Cut;

   ---------------------
   -- Is_Pragma_Check --
   ---------------------

   function Is_Pragma_Check (N : Node_Id; Name : Name_Id) return Boolean is
     (Is_Pragma (N, Pragma_Check)
        and then
      Chars (Get_Pragma_Arg (First (Pragma_Argument_Associations (N))))
      = Name);

   ----------------------
   -- Is_External_Call --
   ----------------------

   function Is_External_Call (N : Node_Id) return Boolean is
      pragma Assert (Is_Protected_Subprogram (Get_Called_Entity (N)));
      --  ??? this should be checked in precondition, but that would create
      --  circular dependency with SPARK_Util.Subprograms; and this routine is
      --  here because a similar Is_Predicate_Function_Call was already here.
      --  Perhaps the organization of the SPARK_Util packages needs rethinking?

      Nam : constant Node_Id := Name (N);
   begin
      --  External calls are those with the selected_component syntax and whose
      --  prefix is anything except a (protected) type.
      return Nkind (Nam) = N_Selected_Component
        and then
          not (Nkind (Prefix (Nam)) in N_Has_Entity
               and then Ekind (Entity (Prefix (Nam))) = E_Protected_Type);
   end Is_External_Call;

   --------------------------------
   -- Is_Predicate_Function_Call --
   --------------------------------

   function Is_Predicate_Function_Call (N : Node_Id) return Boolean is
     (Nkind (N) = N_Function_Call
        and then Is_Predicate_Function (Entity (Name (N))));

   -------------------------------------
   -- Is_Protected_Component_Or_Discr --
   -------------------------------------

   function Is_Protected_Component_Or_Discr (E : Entity_Id) return Boolean is
   begin
      --  Protected discriminants appear either as E_In_Parameter (in spec of
      --  protected types, e.g. in pragma Priority) or as E_Discriminant
      --  (everywhere else).
      return Ekind (E) in E_Component | E_Discriminant | E_In_Parameter
        and then Ekind (Scope (E)) in E_Protected_Type;
   end Is_Protected_Component_Or_Discr;

   ------------------------------
   -- Is_Quantified_Loop_Param --
   ------------------------------

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean is
     (Present (Scope (E))
        and then Present (Parent (Scope (E)))
        and then Nkind (Parent (Scope (E))) = N_Quantified_Expression);

   ---------------------
   -- Is_Synchronized --
   ---------------------

   function Is_Synchronized (E : Entity_Id) return Boolean is
   begin
      return
        Is_Synchronized_Object (E)
          or else Is_Synchronized_State (E)
          or else Is_Part_Of_Concurrent_Object (E)
          or else Ekind (E) in E_Protected_Type | E_Task_Type;
          --  We get protected/task types here when they act as globals for
          --  subprograms nested in the type itself.
   end Is_Synchronized;

   -----------------------------
   -- Iterate_Call_Parameters --
   -----------------------------

   procedure Iterate_Call_Parameters (Call : Node_Id)
   is
      Params     : constant List_Id := Parameter_Associations (Call);
      Cur_Formal : Entity_Id := First_Entity (Get_Called_Entity (Call));
      Cur_Actual : Node_Id := First (Params);
      In_Named   : Boolean := False;
   begin
      --  We have to deal with named arguments, but the frontend has
      --  done some work for us. All unnamed arguments come first and
      --  are given as-is, while named arguments are wrapped into a
      --  N_Parameter_Association. The field First_Named_Actual of the
      --  function or procedure call points to the first named argument,
      --  that should be inserted after the last unnamed one. Each
      --  Named Actual then points to a Next_Named_Actual. These
      --  pointers point directly to the actual, but Next_Named_Actual
      --  pointers are attached to the N_Parameter_Association, so to
      --  get the next actual from the current one, we need to follow
      --  the Parent pointer.
      --
      --  The Boolean In_Named states how to obtain the next actual:
      --  either follow the Next pointer, or the Next_Named_Actual of
      --  the parent.
      --  We start by updating the Cur_Actual and In_Named variables for
      --  the first parameter.

      if Nkind (Cur_Actual) = N_Parameter_Association then
         In_Named := True;
         Cur_Actual := First_Named_Actual (Call);
      end if;

      while Present (Cur_Formal) and then Present (Cur_Actual) loop
         Handle_Parameter (Cur_Formal, Cur_Actual);
         Cur_Formal := Next_Formal (Cur_Formal);

         if In_Named then
            Cur_Actual := Next_Named_Actual (Parent (Cur_Actual));
         else
            Next (Cur_Actual);

            if Nkind (Cur_Actual) = N_Parameter_Association then
               In_Named := True;
               Cur_Actual := First_Named_Actual (Call);
            end if;
         end if;
      end loop;
   end Iterate_Call_Parameters;

   --------------------------------
   -- Iterate_Generic_Parameters --
   --------------------------------

   procedure Iterate_Generic_Parameters (E : Entity_Id)
   is
      Instance : constant Node_Id := Get_Package_Instantiation_Node (E);

      pragma Assert (Nkind (Instance) = N_Package_Instantiation);

      function Get_Label_List (E : Entity_Id) return List_Id;
      --  Use Parent field to reach N_Generic_Package_Declaration
      --  ??? See Gnat2Why.External_Axioms.Get_Label_List

      --------------------
      -- Get_Label_List --
      --------------------

      function Get_Label_List (E : Entity_Id) return List_Id is
         P : Node_Id := Generic_Parent (Package_Specification (E));
      begin
         while Nkind (P) /= N_Generic_Package_Declaration loop
            P := Parent (P);
         end loop;

         return Generic_Formal_Declarations (P);
      end Get_Label_List;

      Params  : constant List_Id := Generic_Associations (Instance);
      Formals : constant List_Id := Get_Label_List (E);

      Param  : Node_Id := First (Params);
      Formal : Node_Id := First (Formals);

   --  Start of processing for Iterate_Generic_Parameters

   begin
      while Present (Param) loop
         pragma Assert (Nkind (Param) = N_Generic_Association);

         Handle_Parameters (Formal, Explicit_Generic_Actual_Parameter (Param));

         Next (Param);
         Next (Formal);
      end loop;
   end Iterate_Generic_Parameters;

   ----------------------------------
   -- Location_In_Standard_Library --
   ----------------------------------

   function Location_In_Standard_Library (Loc : Source_Ptr) return Boolean is
      (case Loc is
          when No_Location =>
             False,

          when Standard_Location | Standard_ASCII_Location | System_Location =>
             True,

          when others =>
             Unit_In_Standard_Library (Unit (Get_Source_File_Index (Loc))));

   ------------------------------------
   -- Number_Of_Assocs_In_Expression --
   ------------------------------------

   function Number_Of_Assocs_In_Expression (N : Node_Id) return Natural is
      Count : Natural := 0;

      function Find_Assoc (N : Node_Id) return Traverse_Result;
      --  Increments Count if N is a N_Component_Association

      ----------------
      -- Find_Assoc --
      ----------------

      function Find_Assoc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Component_Association =>
               Count := Count + 1;
            when others => null;
         end case;
         return OK;
      end Find_Assoc;

      procedure Count_Assoc is new Traverse_Proc (Find_Assoc);

   --  Start of processing for Number_Of_Assocs_In_Expression

   begin
      Count_Assoc (N);
      return Count;
   end Number_Of_Assocs_In_Expression;

   ----------------
   -- Real_Image --
   ----------------

   function Real_Image (U : Ureal; Max_Length : Integer) return String
   is
      Result : String (1 .. Max_Length);
      Last   : Natural := 0;

      procedure Output_Result (S : String);
      --  Callback to print value of U in string Result

      -------------------
      -- Output_Result --
      -------------------

      procedure Output_Result (S : String) is
      begin
         --  Last character is always ASCII.LF which should be ignored
         pragma Assert (S (S'Last) = ASCII.LF);
         Last := Integer'Min (Max_Length, S'Length - 1);
         Result (1 .. Last) := S (S'First .. Last - S'First + 1);
      end Output_Result;

      --  Start of processing for Real_Image

   begin
      Output.Set_Special_Output (Output_Result'Unrestricted_Access);
      UR_Write (U);
      Output.Write_Eol;
      Output.Cancel_Special_Output;
      return Result (1 .. Last);
   end Real_Image;

   ---------------------------
   -- Root_Record_Component --
   ---------------------------

   function Root_Record_Component (E : Entity_Id) return Entity_Id is
      Rec_Type : constant Entity_Id := Retysp (Scope (E));
      Root     : constant Entity_Id := Root_Record_Type (Rec_Type);

   begin
      --  If E is the component of a root type, return it

      if Root = Rec_Type then
         return Search_Component_By_Name (Rec_Type, E);
      end if;

      --  In the component case, it is enough to simply search for the matching
      --  component in the root type, using "Chars".

      if Ekind (E) = E_Component then
         return Search_Component_By_Name (Root, E);
      end if;

      --  In the discriminant case, we need to climb up the hierarchy of types,
      --  to get to the corresponding discriminant in the root type. Note that
      --  there can be more than one corresponding discriminant (because of
      --  renamings), in this case the frontend has picked one for us.

      pragma Assert (Ekind (E) = E_Discriminant);

      declare
         Cur_Type : Entity_Id := Rec_Type;
         Comp     : Entity_Id := E;

      begin
         --  Throughout the loop, maintain the invariant that Comp is a
         --  component of Cur_Type.

         while Cur_Type /= Root loop

            --  If the discriminant Comp constrains a discriminant of the
            --  parent type, then locate the corresponding discriminant of the
            --  parent type by calling Corresponding_Discriminant. This is
            --  needed because both discriminants may not have the same name.

            if Present (Corresponding_Discriminant (Comp)) then
               Comp     := Corresponding_Discriminant (Comp);
               Cur_Type := Retysp (Scope (Comp));

            --  Otherwise, just climb the type derivation/subtyping chain

            else
               declare
                  Old_Type : constant Entity_Id := Cur_Type;
               begin
                  Cur_Type := (if Full_View_Not_In_SPARK (Cur_Type)
                               then Get_First_Ancestor_In_SPARK (Cur_Type)
                               else Retysp (Etype (Cur_Type)));
                  pragma Assert (Cur_Type /= Old_Type);
                  Comp := Search_Component_By_Name (Cur_Type, Comp);
               end;
            end if;
         end loop;

         return Comp;
      end;
   end Root_Record_Component;

   ---------------------
   -- Safe_First_Sloc --
   ---------------------

   function Safe_First_Sloc (N : Node_Id) return Source_Ptr is
     (if Instantiation_Location (Sloc (N)) = No_Location
      then First_Sloc (N)
      else Sloc (First_Node (N)));

   ------------------------------
   -- Search_Component_By_Name --
   ------------------------------

   function Search_Component_By_Name
     (Rec  : Entity_Id;
      Comp : Entity_Id) return Entity_Id
   is
      Specific_Rec : constant Entity_Id :=
        (if Is_Class_Wide_Type (Rec)
         then Retysp (Get_Specific_Type_From_Classwide (Rec))
         else Rec);

      --  Check that it is safe to call First_Component_Or_Discriminant on
      --  Specific_Rec.

      pragma Assert
        (Is_Concurrent_Type (Specific_Rec)
         or else Is_Incomplete_Or_Private_Type (Specific_Rec)
         or else Is_Record_Type (Specific_Rec)
         or else Has_Discriminants (Specific_Rec));

      Cur_Comp     : Entity_Id :=
        First_Component_Or_Discriminant (Specific_Rec);
   begin
      while Present (Cur_Comp) loop
         if Chars (Cur_Comp) = Chars (Comp) then

            --  We have found a field with the same name. If the type is not
            --  tagged, we have found the correct component. Otherwise, either
            --  it has the same Original_Record_Component and it is the field
            --  we were looking for or it does not and Comp is not in Rec.

            if not Is_Tagged_Type (Rec)
               or else Original_Record_Component (Cur_Comp) =
                 Original_Record_Component (Comp)
            then
               return Cur_Comp;
            else
               return Empty;
            end if;
         end if;

         Next_Component_Or_Discriminant (Cur_Comp);
      end loop;

      return Empty;
   end Search_Component_By_Name;

   -----------------
   -- Source_Name --
   -----------------

   function Source_Name (E : Entity_Id) return String is

      function Short_Name (E : Entity_Id) return String;
      --  @return the uncapitalized unqualified name for E

      ----------------
      -- Short_Name --
      ----------------

      function Short_Name (E : Entity_Id) return String is
      begin
         Get_Unqualified_Name_String (Chars (E));
         return Name_Buffer (1 .. Name_Len);
      end Short_Name;

   --  Start of processing for Source_Name

   begin
      if E = Empty then
         return "";
      end if;

      declare
         Name : String := Short_Name (E);
         Loc  : Source_Ptr := Sloc (E);
         Buf  : Source_Buffer_Ptr;
      begin
         if Name /= "" and then Loc >= First_Source_Ptr then
            Buf := Source_Text (Get_Source_File_Index (Loc));

            --  Copy characters from source while they match (modulo
            --  capitalization) the name of the entity.

            for Idx in Name'Range loop
               exit when not Identifier_Char (Buf (Loc))
                 or else Fold_Lower (Buf (Loc)) /= Name (Idx);
               Name (Idx) := Buf (Loc);
               Loc := Loc + 1;
            end loop;
         end if;

         return Name;
      end;
   end Source_Name;

   --------------------
   -- Spec_File_Name --
   --------------------

   function Spec_File_Name (N : Node_Id) return String is
      CU : Node_Id := Enclosing_Lib_Unit_Node (N);

   begin
      case Nkind (Unit (CU)) is
         when N_Package_Body =>
            CU := Library_Unit (CU);
         when others =>
            null;
      end case;

      return File_Name (Sloc (CU));
   end Spec_File_Name;

   -----------------------------------
   -- Spec_File_Name_Without_Suffix --
   -----------------------------------

   function Spec_File_Name_Without_Suffix (N : Node_Id) return String is
     (File_Name_Without_Suffix (Spec_File_Name (N)));

   --------------------
   -- String_Of_Node --
   --------------------

   function String_Of_Node (N : Node_Id) return String is

      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String;

      function Real_Image_10 (U : Ureal) return String is
         (Real_Image (U, 10));

      function String_Image (S : String_Id) return String is
        ('"' & Get_Name_String (String_To_Name (S)) & '"');

      function Node_To_String is new
        Expression_Image (Real_Image_10, String_Image, Ident_Image);
      --  The actual printing function

      -----------------
      -- Ident_Image --
      -----------------

      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String
      is
         pragma Unreferenced (Orig_Expr, Expand_Type);
      begin
         if Nkind (Expr) = N_Defining_Identifier then
            return Source_Name (Expr);
         elsif Present (Entity (Expr)) then
            return Source_Name (Entity (Expr));
         else
            return Get_Name_String (Chars (Expr));
         end if;
      end Ident_Image;

   --  Start of processing for String_Of_Node

   begin
      return Node_To_String (N, "");
   end String_Of_Node;

   ------------------
   -- String_Value --
   ------------------

   function String_Value (Str_Id : String_Id) return String is
   begin
      --  ??? pragma Assert (Str_Id /= No_String);

      if Str_Id = No_String then
         return "";
      end if;

      String_To_Name_Buffer (Str_Id);

      return Name_Buffer (1 .. Name_Len);
   end String_Value;

   ----------------------------------
   -- Is_Part_Of_Concurrent_Object --
   ----------------------------------

   function Is_Part_Of_Concurrent_Object (E : Entity_Id) return Boolean is
   begin
      if Ekind (E) in E_Abstract_State | E_Constant | E_Variable then
         declare
            Encapsulating : constant Entity_Id := Encapsulating_State (E);

         begin
            return Present (Encapsulating)
              and then Ekind (Encapsulating) = E_Variable
              and then Ekind (Etype (Encapsulating)) in E_Protected_Type
                                                      | E_Task_Type;
         end;

      else
         return False;
      end if;
   end Is_Part_Of_Concurrent_Object;

   ---------------------------------
   -- Is_Part_Of_Protected_Object --
   ---------------------------------

   function Is_Part_Of_Protected_Object (E : Entity_Id) return Boolean is
   begin
      if Ekind (E) in E_Abstract_State | E_Constant | E_Variable then
         declare
            Encapsulating : constant Entity_Id := Encapsulating_State (E);

         begin
            return Present (Encapsulating)
              and then Ekind (Encapsulating) = E_Variable
              and then Ekind (Etype (Encapsulating)) = E_Protected_Type;
         end;

      else
         return False;
      end if;
   end Is_Part_Of_Protected_Object;

end SPARK_Util;
