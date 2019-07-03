------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2011-2019, AdaCore                     --
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

with Ada.Characters.Latin_1; use Ada.Characters.Latin_1;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Csets;                  use Csets;
with Errout;                 use Errout;
with Flow_Utility;           use Flow_Utility;
with Gnat2Why_Args;
with Lib.Xref;
with Opt;
with Osint;
with Output;
with Pprint;                 use Pprint;
with Sem_Ch12;               use Sem_Ch12;
with Sem_Eval;               use Sem_Eval;
with Sem_Prag;               use Sem_Prag;
with Sem_Type;               use Sem_Type;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Util.Types;       use SPARK_Util.Types;
with Stand;                  use Stand;
with Stringt;                use Stringt;
with Flow_Dependency_Maps;   use Flow_Dependency_Maps;
with Flow_Types;             use Flow_Types;
with Flow_Refinement;        use Flow_Refinement;

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

   ---------------------------
   -- Append_Multiple_Index --
   ---------------------------

   function Append_Multiple_Index (S : String) return String is
   begin
      if Opt.Multiple_Unit_Index = 0 then
         return S;
      end if;
      declare
         Int_Str : constant String := Int'Image (Opt.Multiple_Unit_Index);
      begin
         return S & Osint.Multi_Unit_Index_Character &
           Int_Str (Int_Str'First + 1 .. Int_Str'Last);
      end;
   end Append_Multiple_Index;

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

   ----------------------
   -- Canonical_Entity --
   ----------------------

   function Canonical_Entity
     (Ref     : Entity_Id;
      Context : Entity_Id)
      return Entity_Id
   is
   begin
      if Is_Single_Concurrent_Object (Ref)
        and then Is_CCT_Instance (Ref_Id => Etype (Ref), Context_Id => Context)
      then
         return Etype (Ref);
      elsif Has_Non_Limited_View (Ref) then
         --  ??? this partly duplicates a similar transformatioin in
         --  Direct_Mapping_Id; maybe it should be done once, in SPARK_Rewrite.
         return Unique_Entity (Non_Limited_View (Ref));
      else
         return Unique_Entity (Ref);
      end if;
   end Canonical_Entity;

   ----------------------------------
   -- Candidate_For_Loop_Unrolling --
   ----------------------------------

   procedure Candidate_For_Loop_Unrolling
     (Loop_Stmt   : Node_Id;
      Output_Info : Boolean;
      Result      : out Unrolling_Type;
      Low_Val     : out Uint;
      High_Val    : out Uint)
   is
      Reason : Unbounded_String;
      --  Reason to output for not unrolling the loop

      -----------------------
      -- Local Subprograms --
      -----------------------

      function Is_Applicable_Loop_Variant_Or_Invariant
        (N : Node_Id) return Traverse_Result;
      --  Returns Abandon when a loop (in)variant applicable to the loop is
      --  encountered and OK otherwise.

      function Is_Non_Scalar_Object_Declaration
        (N : Node_Id) return Traverse_Result;
      --  Returns Abandon when an object declaration of a non-scalar type is
      --  encountered and OK otherwise. Update [Reason] accordingly.

      ---------------------------------------------
      -- Is_Applicable_Loop_Variant_Or_Invariant --
      ---------------------------------------------

      function Is_Applicable_Loop_Variant_Or_Invariant
        (N : Node_Id) return Traverse_Result
      is
         Par : Node_Id;
      begin
         if Is_Pragma_Check (N, Name_Loop_Invariant)
           or else Is_Pragma (N, Pragma_Loop_Variant)
         then
            Par := N;
            while Nkind (Par) /= N_Loop_Statement loop
               Par := Parent (Par);
            end loop;

            if Par = Loop_Stmt then
               return Abandon;
            end if;
         end if;

         return OK;
      end Is_Applicable_Loop_Variant_Or_Invariant;

      function Find_Applicable_Loop_Variant_Or_Invariant is new
        Traverse_More_Func (Is_Applicable_Loop_Variant_Or_Invariant);

      --------------------------------------
      -- Is_Non_Scalar_Object_Declaration --
      --------------------------------------

      function Is_Non_Scalar_Object_Declaration
        (N : Node_Id) return Traverse_Result
      is
      begin
         case Nkind (N) is
            when N_Object_Declaration =>
               if not Is_Scalar_Type (Etype (Defining_Identifier (N))) then
                  Error_Msg_Sloc := Sloc (N);
                  Reason :=
                    To_Unbounded_String ("local non-scalar declaration #");
                  return Abandon;
               end if;

            when others =>
               null;
         end case;

         return OK;
      end Is_Non_Scalar_Object_Declaration;

      function Find_Non_Scalar_Object_Declaration is new
        Traverse_More_Func (Is_Non_Scalar_Object_Declaration);

      ---------------------
      -- Local Variables --
      ---------------------

      Scheme     : constant Node_Id := Iteration_Scheme (Loop_Stmt);
      Loop_Spec  : constant Node_Id :=
        (if Present (Scheme) and then No (Condition (Scheme)) then
           Loop_Parameter_Specification (Scheme)
         else Empty);
      Over_Range : constant Boolean := Present (Loop_Spec);
      Over_Node  : constant Node_Id :=
        (if Over_Range then Discrete_Subtype_Definition (Loop_Spec)
         else Empty);

      Low, High     : Node_Id;
      Dynamic_Range : Boolean := False;

   --  Start of processing for Candidate_For_Unrolling

   begin
      Low_Val  := No_Uint;
      High_Val := No_Uint;
      Result   := No_Unrolling;

      --  Only simple FOR loops can be unrolled. Simple loops are
      --  defined as having no (in)variant...

      if Over_Range
        and then Find_Applicable_Loop_Variant_Or_Invariant (Loop_Stmt)
                 /= Abandon
      then
         Low  := Low_Bound (Get_Range (Over_Node));
         High := High_Bound (Get_Range (Over_Node));

         --  and the low bound is static, or consider instead the low bound of
         --  its type...

         if not Compile_Time_Known_Value (Low) then
            Low := Type_Low_Bound (Etype (Low));
            Dynamic_Range := True;
         end if;

         --  and the high bound is static, or consider instead the high bound
         --  of its type...

         if not Compile_Time_Known_Value (High) then
            High := Type_High_Bound (Etype (High));
            Dynamic_Range := True;
         end if;

         --  and compile-time known bounds, with a small number of
         --  iterations...

         if Compile_Time_Known_Value (Low)
           and then Compile_Time_Known_Value (High)
         then
            Low_Val  := Expr_Value (Low);
            High_Val := Expr_Value (High);

            if Low_Val <= High_Val
              and then High_Val < Low_Val + Gnat2Why_Args.Max_Loop_Unrolling

              --  (also checking that the bounds fit in an Int, so that we can
              --  convert them using UI_To_Int)

              and then Low_Val >= UI_From_Int (Int'First)
              and then High_Val <= UI_From_Int (Int'Last)
            then
               --  and either the loop is from 1 to 1, or more generally from
               --  a value to the same value (a trick to emulate forward gotos,
               --  by exiting from the loop instead) so that there are no
               --  issues with the type of an object declared in the loop
               --  having contradictory constraints across loop iterations

               if Low_Val = High_Val

               --  or there are no non-scalar object declarations, precisely to
               --  avoid that their types have contradictory constraints across
               --  loop iterations.

                 or else Find_Non_Scalar_Object_Declaration (Loop_Stmt)
                   /= Abandon
               then
                  --  Loop can be unrolled. Decide the type of unrolling based
                  --  on whether the range is static or dynamic.

                  Result := (if Dynamic_Range then Unrolling_With_Condition
                             else Simple_Unrolling);
               end if;

            else
               if High_Val >= Low_Val + Gnat2Why_Args.Max_Loop_Unrolling then
                  Reason := To_Unbounded_String ("too many loop iterations");
               else
                  Reason := To_Unbounded_String ("value of loop bounds");
               end if;
            end if;

         else
            Reason := To_Unbounded_String ("dynamic loop bounds");
         end if;

         if Output_Info then
            if Result /= No_Unrolling then
               Error_Msg_N ("info: ?unrolling loop", Loop_Stmt);

            elsif Reason /= "" then
               Error_Msg_N
                 ("info: ?cannot unroll loop (" & To_String (Reason) & ")",
                  Loop_Stmt);

            else
               Error_Msg_N ("info: ?cannot unroll loop", Loop_Stmt);
            end if;
         end if;
      end if;
   end Candidate_For_Loop_Unrolling;

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
      --  Hidden discriminants are only in SPARK if Ty's full view is in SPARK

      if Ekind (E) = E_Discriminant then
         if Has_Discriminants (Ty) then
            return True;
         else
            pragma Assert (Has_Discriminants (Full_View (Ty)));
            return Entity_In_SPARK (Full_View (Ty));
         end if;

      --  Components of a protected type are visible except if the type full
      --  view is not in SPARK.

      elsif Is_Protected_Type (Ty) then

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

   ------------------------
   -- Contains_Allocator --
   ------------------------

   function Contains_Allocator (N : Node_Id) return Boolean is

      function Is_Allocator (N : Node_Id) return Traverse_Result;
      --  Will return Abandon if we encounter an allocator

      -------------
      -- Process --
      -------------

      function Is_Allocator (N : Node_Id) return Traverse_Result
      is
      begin
         if Nkind (N) = N_Allocator then
            return Abandon;
         else
            return OK;
         end if;
      end Is_Allocator;

      function Check_Allocator is new
        Traverse_More_Func (Is_Allocator);

   begin
      return Check_Allocator (N) = Abandon;
   end Contains_Allocator;

   -------------------------------------
   -- Contains_Volatile_Function_Call --
   -------------------------------------

   function Contains_Volatile_Function_Call (N : Node_Id) return Boolean is

      function Is_Volatile_Function_Call (N : Node_Id) return Traverse_Result;
      --  Will return Abandon if we encounter a call to a function with
      --  Volatile_Function set.

      -------------
      -- Process --
      -------------

      function Is_Volatile_Function_Call (N : Node_Id) return Traverse_Result
      is
      begin
         if Nkind (N) = N_Function_Call
           and then Is_Enabled_Pragma
             (Get_Pragma (Get_Called_Entity (N), Pragma_Volatile_Function))
         then
            return Abandon;
         else
            return OK;
         end if;
      end Is_Volatile_Function_Call;

      function Check_Volatile_Function is new
        Traverse_More_Func (Is_Volatile_Function_Call);

   begin
      return Check_Volatile_Function (N) = Abandon;
   end Contains_Volatile_Function_Call;

   --------------------------------------------
   -- Declaration_Is_Associated_To_Parameter --
   --------------------------------------------

   function Declaration_Is_Associated_To_Parameter
     (N : Node_Id) return Boolean
   is
      (Nkind (N) in N_Entity
        and then Ekind (N) in Type_Kind | E_Constant | E_Variable
        and then Present (Related_Expression (N))
        and then Nkind (Related_Expression (N)) in N_Entity
        and then Is_Formal (Related_Expression (N)));

   --------------------------------------------
   -- Directly_Enclosing_Subprogram_Or_Entry --
   --------------------------------------------

   function Directly_Enclosing_Subprogram_Or_Entry
     (E : Entity_Id) return Entity_Id
   is
      S : Entity_Id := Scope (E);
   begin
      loop
         if No (S) then
            return Empty;
         elsif Ekind (S) in Entry_Kind
                          | E_Function
                          | E_Procedure
         then
            return S;
         elsif Ekind (S) = E_Package then
            S := Scope (S);
         else
            return Empty;
         end if;
      end loop;
   end Directly_Enclosing_Subprogram_Or_Entry;

   -------------------------------
   -- Enclosing_Concurrent_Type --
   -------------------------------

   function Enclosing_Concurrent_Type (E : Entity_Id) return Entity_Id is
     (if Is_Part_Of_Concurrent_Object (E)
      then Etype (Encapsulating_State (E))
      else Scope (E));

   --------------------------------
   -- Enclosing_Generic_Instance --
   --------------------------------

   function Enclosing_Generic_Instance (E : Entity_Id) return Entity_Id is
      S : Entity_Id := Scope (E);
   begin
      loop
         if No (S) then
            return Empty;
         elsif Is_Generic_Instance (S) then
            return S;
         else
            S := Scope (S);
         end if;
      end loop;
   end Enclosing_Generic_Instance;

   --------------------
   -- Enclosing_Unit --
   --------------------

   function Enclosing_Unit (E : Entity_Id) return Entity_Id is
      S : Entity_Id := Scope (E);

   begin
      loop
         if Ekind (S) in Entry_Kind
                       | E_Function
                       | E_Procedure
                       | E_Package
                       | E_Protected_Type
                       | E_Task_Type
         then
            --  We have found the enclosing unit, return it

            return S;
         else
            pragma Assert (not Is_Generic_Unit (S));

            --  Go to the enclosing scope

            S := Scope (S);
         end if;
      end loop;
   end Enclosing_Unit;

   -------------------------------
   -- Entity_To_Subp_Assumption --
   -------------------------------

   function Entity_To_Subp_Assumption (E : Entity_Id) return Subp_Type is
      function Loc_To_Assume_Sloc (Loc : Source_Ptr) return My_Sloc
        with Pre => Loc /= No_Location;

      ------------------------
      -- Loc_To_Assume_Sloc --
      ------------------------

      function Loc_To_Assume_Sloc (Loc : Source_Ptr) return My_Sloc is
         Sloc : My_Sloc := Sloc_Lists.Empty_List;
         Slc  : Source_Ptr := Loc;
      begin
         loop
            declare
               File : constant String := File_Name (Slc);
               Line : constant Positive :=
                 Positive (Get_Physical_Line_Number (Slc));
            begin
               Sloc.Append (Mk_Base_Sloc (File => File, Line => Line));
            end;
            Slc := Instantiation_Location (Slc);

            exit when Slc = No_Location;
         end loop;
         return Sloc;
      end Loc_To_Assume_Sloc;
   begin
      return Mk_Subp (Name => Full_Source_Name (E),
                      Sloc => Loc_To_Assume_Sloc (Sloc (E)));
   end Entity_To_Subp_Assumption;

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

   --------------------------------
   -- First_Parent_With_Property --
   --------------------------------

   function First_Parent_With_Property (N : Node_Id) return Node_Id is
      P : Node_Id := N;
   begin
      loop
         P := Parent (P);
         exit when No (P) or else Property (P);
      end loop;
      return P;
   end First_Parent_With_Property;

   ---------------------
   -- Full_Entry_Name --
   ---------------------

   function Full_Entry_Name (N : Node_Id) return String is
   begin
      case Nkind (N) is
         --  Once we get to the root of the prefix, which can be either a
         --  simple identifier (e.g. "PO") or an expanded name (e.g.
         --  Pkg1.Pkg2.PO), return the unique name of the target object.

         when N_Expanded_Name
            | N_Identifier
         =>
            declare
               Obj : constant Entity_Id := Entity (N);
               --  Object that is the target of an entry call; it must be a
               --  variable with protected components.

               pragma Assert (Ekind (Obj) = E_Variable
                                and then Has_Protected (Etype (Obj)));

            begin
               return Unique_Name (Obj);
            end;

         --  Accesses to array components are not known statically (because
         --  flow analysis can't determine exact values of the indices); by
         --  ignoring them we conservatively consider accesses to different
         --  components as potential violations.

         when N_Indexed_Component =>
            return Full_Entry_Name (Prefix (N));

         --  Accesses to record components are known statically and become part
         --  of the returned identifier.

         when N_Selected_Component =>
            return Full_Entry_Name (Prefix (N)) &
              "__" & Get_Name_String (Chars (Entity (Selector_Name (N))));

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
     ((Is_Type (E) and then Is_Standard_Boolean_Type (E))
        or else
      E = Universal_Fixed);

   ----------------------
   -- Full_Source_Name --
   ----------------------

   function Full_Source_Name (E : Entity_Id) return String is
      Name : constant String := Source_Name (E);

   begin
      if E = Standard_Standard
        or else Has_Fully_Qualified_Name (E)
        or else Scope (E) = Standard_Standard
      then
         return Name;
      else
         return Full_Source_Name (Scope (E)) & "." & Name;
      end if;
   end Full_Source_Name;

   --------------------------------
   -- Generic_Actual_Subprograms --
   --------------------------------

   function Generic_Actual_Subprograms (E : Entity_Id) return Node_Sets.Set is
      Results : Node_Sets.Set;

      Instance : constant Node_Id := Get_Unit_Instantiation_Node (E);

      pragma Assert (Nkind (Instance) in N_Generic_Instantiation);

      Actuals : constant List_Id := Generic_Associations (Instance);

      Actual : Node_Id := First (Actuals);

   begin

      while Present (Actual) loop
         pragma Assert (Nkind (Actual) = N_Generic_Association);

         declare
            Actual_Expl : constant Node_Id :=
              Explicit_Generic_Actual_Parameter (Actual);

         begin
            if Nkind (Actual_Expl) in N_Has_Entity then
               declare
                  E_Actual : constant Entity_Id := Entity (Actual_Expl);

               begin
                  if Present (E_Actual)
                    and then Ekind (E_Actual) in E_Function
                                               | E_Procedure
                  then

                     --  Generic actual subprograms are typically renamings and
                     --  then we want the renamed subprogram, but for generics
                     --  nested in other generics they seem to directly point
                     --  to what we need.

                     declare
                        Renamed : constant Entity_Id :=
                          Renamed_Entity (E_Actual);
                        --  For subprograms Renamed_Entity is set transitively,
                        --  so we just need to call it once.

                     begin
                        Results.Include (if Present (Renamed)
                                         then Renamed
                                         else E_Actual);
                     end;
                  end if;
               end;
            end if;
         end;

         Next (Actual);
      end loop;

      return Results;
   end Generic_Actual_Subprograms;

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

   ----------------------------
   -- Get_Formal_From_Actual --
   ----------------------------

   function Get_Formal_From_Actual (Actual : Node_Id) return Entity_Id is
      Formal : Entity_Id := Empty;

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

      pragma Assert (Present (Formal));
      return Formal;
   end Get_Formal_From_Actual;

   ----------------------------
   -- Get_Initialized_Object --
   ----------------------------

   function Get_Initialized_Object (N : Node_Id) return Entity_Id is
      Par : Node_Id := Parent (N);

   begin
      --  The object declaration might be the parent expression of the
      --  aggregate, or there might be a qualification in between. Deal
      --  uniformly with both cases.

      if Nkind (Par) = N_Qualified_Expression then
         Par := Parent (Par);
      end if;

      if Nkind (Par) = N_Object_Declaration then
         return Defining_Identifier (Par);
      else
         return Empty;
      end if;
   end Get_Initialized_Object;

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
                    when Object_Kind                => Etype (N),
                    when Scalar_Kind                => N,
                    when E_Limited_Private_Subtype
                       | E_Limited_Private_Type
                       | E_Private_Subtype
                       | E_Private_Type             => Full_View (N),
                    when others                     => raise Program_Error));

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
      elsif Is_Object (E) then
        Is_Effectively_Volatile (E)
      else
        Is_Effectively_Volatile_Object (E));

   ---------------------------
   -- Has_Volatile_Property --
   ---------------------------

   function Has_Volatile_Property (E : Checked_Entity_Id;
                                   P : Volatile_Pragma_Id)
                                   return Boolean
   is
   begin
      --  Q: Why restrict the property of volatility for IN and OUT parameters?
      --
      --  A: See SRM 7.1.3. In short when passing a volatile through a
      --  parameter we present a 'worst case but sane' view of the volatile,
      --  which means there should be no information hiding possible and no
      --  silent side effects, so...

      case Ekind (E) is
         when E_Abstract_State | E_Variable | E_Component =>
            return
              (case P is
               when Pragma_Async_Readers    => Async_Readers_Enabled (E),
               when Pragma_Async_Writers    => Async_Writers_Enabled (E),
               when Pragma_Effective_Reads  => Effective_Reads_Enabled (E),
               when Pragma_Effective_Writes => Effective_Writes_Enabled (E));

         when E_In_Parameter  =>
            --  All volatile in parameters have only async_writers set. In
            --  particular reads cannot be effective and the absence of AR is
            --  irrelevant since we are not allowed to write to it anyway.
            return P = Pragma_Async_Writers;

         when E_Out_Parameter =>
            --  Out parameters we assume that writes are effective (worst
            --  case). We do not assume reads are effective because (a - it may
            --  be illegal to read anyway, b - we ban passing a fully volatile
            --  object as an argument to an out parameter).
            return P in Pragma_Async_Readers | Pragma_Effective_Writes;

         when E_In_Out_Parameter =>
            --  For in out we just assume the absolute worst case (fully
            --  volatile).
            return True;

         when others =>
            raise Program_Error;
      end case;
   end Has_Volatile_Property;

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
        and then Nkind (Parent (N)) in N_Type_Conversion
                                     | N_Unchecked_Type_Conversion
        and then Present (Parent (Parent (N)))
        and then Is_Predicate_Function_Call (Parent (Parent (N))));

   --------------------------------------
   -- Is_Concurrent_Component_Or_Discr --
   --------------------------------------

   function Is_Concurrent_Component_Or_Discr (E : Entity_Id) return Boolean is
   begin
      --  Protected discriminants appear either as E_In_Parameter (in spec of
      --  protected types, e.g. in pragma Priority) or as E_Discriminant
      --  (everywhere else).
      return Ekind (E) in E_Component | E_Discriminant | E_In_Parameter
        and then Ekind (Scope (E)) in E_Protected_Type | E_Task_Type;
   end Is_Concurrent_Component_Or_Discr;

   ----------------------------
   -- Is_Declared_In_Private --
   ----------------------------

   function Is_Declared_In_Private (E : Entity_Id) return Boolean is
      Current : Entity_Id := E;
   begin
      loop
         declare
            Decl : constant Node_Id :=
              (if Is_Itype (Current) then Associated_Node_For_Itype (Current)
               else Enclosing_Declaration (Current));
         begin
            if In_Private_Declarations (Decl) then
               return True;
            end if;
            Current := Scope (Current);
            exit when No (Current);
         end;
      end loop;
      return False;
   end Is_Declared_In_Private;

   -------------------------
   -- Is_Declared_In_Unit --
   -------------------------

   --  Parameters of subprograms cannot be local to a unit. Discriminants of
   --  concurrent objects are not local to the object.

   function Is_Declared_In_Unit
     (E     : Entity_Id;
      Scope : Entity_Id) return Boolean
   is
     (Enclosing_Unit (E) = Scope and then not Is_Formal (E)
      and then (Ekind (E) /= E_Discriminant or else Sinfo.Scope (E) /= Scope));

   ----------------------------------
   -- Is_Declared_In_Main_Lib_Unit --
   ----------------------------------

   function Is_Declared_In_Main_Lib_Unit (N : Node_Id) return Boolean is
      Main_CU : Entity_Id := Main_Unit_Entity;
      N_CU    : Entity_Id :=
        Unique_Defining_Entity (Unit (Enclosing_Lib_Unit_Node (N)));

   begin
      --  If the current compilation unit is a child unit, go to its parent

      while Is_Child_Unit (Main_CU) loop
         Main_CU := Unique_Defining_Entity
           (Unit (Enclosing_Lib_Unit_Node (Scope (Main_CU))));
      end loop;

      --  If the enclosing unit of N is a child unit, go to its parent

      while Is_Child_Unit (N_CU) loop
         N_CU := Unique_Defining_Entity
           (Unit (Enclosing_Lib_Unit_Node (Scope (N_CU))));
      end loop;

      return N_CU = Main_CU;
   end Is_Declared_In_Main_Lib_Unit;

   ---------------------
   -- Is_Empty_Others --
   ---------------------

   function Is_Empty_Others (N : Node_Id) return Boolean
   is
      First_Choice : constant Node_Id := First (Discrete_Choices (N));
   begin
      return
        Nkind (First_Choice) = N_Others_Choice
        and then Is_Empty_List (Others_Discrete_Choices (First_Choice));
   end Is_Empty_Others;

   ----------------------------------
   -- Is_Error_Signaling_Statement --
   ----------------------------------

   function Is_Error_Signaling_Statement (N : Node_Id) return Boolean is
   begin
      case Nkind (N) is
         when N_Raise_xxx_Error | N_Raise_Statement =>
            return True;

         when N_Pragma =>
            if Is_Pragma_Check (N, Name_Assert) then
               declare
                  Arg1 : constant Node_Id :=
                    First (Pragma_Argument_Associations (N));
                  Arg2 : constant Node_Id := Next (Arg1);
                  Expr : constant Node_Id := Expression (Arg2);
               begin
                  return Compile_Time_Known_Value (Expr)
                    and then Expr_Value (Expr) = Uint_0;
               end;
            else
               return False;
            end if;

         when N_Procedure_Call_Statement =>
            return Is_Error_Signaling_Procedure (Get_Called_Entity (N));

         when others =>
            return False;
      end case;
   end Is_Error_Signaling_Statement;

   ----------------------
   -- Is_External_Call --
   ----------------------

   function Is_External_Call (N : Node_Id) return Boolean is
      Nam : constant Node_Id := Name (N);
   begin
      --  External calls are those with the selected_component syntax and whose
      --  prefix is anything except a (protected) type.
      return Nkind (Nam) = N_Selected_Component
        and then
          not (Nkind (Prefix (Nam)) in N_Has_Entity
               and then Ekind (Entity (Prefix (Nam))) = E_Protected_Type);
   end Is_External_Call;

   ----------------------
   -- Is_Global_Entity --
   ----------------------

   function Is_Global_Entity (E : Entity_Id) return Boolean is
     (Is_Heap_Variable (E)
        or else
      Ekind (E) in E_Loop_Parameter
                 | E_Variable
                 | Formal_Kind
                 | E_Protected_Type
                 | E_Task_Type
        or else
      (Ekind (E) = E_Constant and then Has_Variable_Input (E))
        or else
      (Ekind (E) = E_Abstract_State and then not Is_Null_State (E)));
   --  ??? this could be further restricted basen on what may appear in
   --  Proof_In, Input, and Output.

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

   ----------------------------------
   -- Is_In_Statically_Dead_Branch --
   ----------------------------------

   function Is_In_Statically_Dead_Branch (N : Node_Id) return Boolean is
      Anc : Node_Id := Parent (N);
      Prev : Node_Id := N;

      function Comes_From_Dead_Branch (If_Stmt, Stmt : Node_Id) return Boolean
        with Pre => Nkind (If_Stmt) = N_If_Statement;
      --  @param If_Stmt an if statement node
      --  @param Stmt a statement node
      --  @return True iff the if-statement contains a statically dead branch
      --      and the statement is at the top-level of the corresponding branch

      function Comes_From_This_Dead_Branch
        (If_Stmt, Stmt : Node_Id)
         return Boolean
        with Pre => Nkind (If_Stmt) in N_If_Statement | N_Elsif_Part;
      --  @param If_Stmt an if statement or els_if part
      --  @param Stmt a statement node
      --  @return True iff the "then" condition of the statement or part is
      --      statically dead and contains the Stmt node

      function Has_True_Condition (If_Stmt : Node_Id) return Boolean
        with Pre => Nkind (If_Stmt) = N_If_Statement;
      --  @param If_Stmt an if statement node
      --  @return True iff the main condition or any of the elsif conditions is
      --    statically true

      ----------------------------
      -- Comes_From_Dead_Branch --
      ----------------------------

      function Comes_From_Dead_Branch (If_Stmt, Stmt : Node_Id) return Boolean
      is
      begin
         --  check if then branch is dead and contains our stmt
         if Comes_From_This_Dead_Branch (If_Stmt, Stmt) then
            return True;
         end if;
         --  check if any of the elsif branches is dead and contains our stmt
         if Present (Elsif_Parts (If_Stmt)) then
            declare
               Elt : Node_Id := First (Elsif_Parts (If_Stmt));
            begin
               while Present (Elt) loop
                  if Comes_From_This_Dead_Branch (Elt, Stmt) then
                     return True;
                  end if;
                  Next (Elt);
               end loop;
            end;
         end if;
         --  check if the else branch is dead and contains our stmt
         if List_Containing (Stmt) = Else_Statements (If_Stmt)
           and then Has_True_Condition (If_Stmt)
         then
            return True;
         end if;
         return False;
      end Comes_From_Dead_Branch;

      ---------------------------------
      -- Comes_From_This_Dead_Branch --
      ---------------------------------

      function Comes_From_This_Dead_Branch
        (If_Stmt, Stmt : Node_Id)
         return Boolean
      is (Nkind (Condition (If_Stmt)) = N_Identifier
           and then Entity (Condition (If_Stmt)) = Standard_False
           and then List_Containing (Stmt) = Then_Statements (If_Stmt));

      ------------------------
      -- Has_True_Condition --
      ------------------------

      function Has_True_Condition (If_Stmt : Node_Id) return Boolean is
      begin
         if Nkind (Condition (If_Stmt)) = N_Identifier
           and then Entity (Condition (If_Stmt)) = Standard_True
         then
            return True;
         end if;
         if Present (Elsif_Parts (If_Stmt)) then
            declare
               Elt : Node_Id := First (Elsif_Parts (If_Stmt));
            begin
               while Present (Elt) loop
                  if Nkind (Condition (Elt)) = N_Identifier
                    and then Entity (Condition (Elt)) = Standard_True
                  then
                     return True;
                  end if;
                  Next (Elt);
               end loop;
            end;
         end if;
         return False;
      end Has_True_Condition;

      subtype Subprogram_Boundary is Node_Kind
        with Static_Predicate => Subprogram_Boundary in
          N_Subprogram_Body | N_Protected_Body | N_Entry_Body | N_Package_Body;
   begin
      while Nkind (Anc) not in Subprogram_Boundary and then Present (Anc) loop
         if Nkind (Anc) = N_If_Statement
           and then Comes_From_Dead_Branch (Anc, Prev)
         then
            return True;
         end if;
         Prev := Anc;
         Anc := Parent (Anc);
      end loop;
      return False;
   end Is_In_Statically_Dead_Branch;

   -----------------------
   -- Is_Local_Borrower --
   -----------------------

   function Is_Local_Borrower (E : Entity_Id) return Boolean is
      T : constant Entity_Id := Retysp (Etype (E));
   begin
      return Ekind (E) in E_Variable | E_Constant
        and then Is_Access_Type (T)
        and then not Is_Access_Constant (T)
        and then Is_Anonymous_Access_Type (T);
   end Is_Local_Borrower;

   ---------------------------------
   -- Is_Not_Hidden_Discriminant  --
   ---------------------------------

   function Is_Not_Hidden_Discriminant (E : Entity_Id) return Boolean is
     (not (Ekind (E) = E_Discriminant and then
              (Is_Completely_Hidden (E)
                or else No (Root_Record_Component (E)))));

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
     ((case Ekind (E) is
          when E_Abstract_State => True,
          when E_Constant       => Ekind (Scope (E)) = E_Package
                                   and then not In_Generic_Actual (E)
                                   and then Has_Variable_Input (E),
          when E_Variable       => Ekind (Scope (E)) = E_Package,
          when others           => False)
      and then
        not Is_Internal (E));

   ---------------
   -- Is_Pragma --
   ---------------

   function Is_Pragma (N : Node_Id; Name : Pragma_Id) return Boolean is
     (Nkind (N) = N_Pragma
        and then Get_Pragma_Id (Pragma_Name (N)) = Name);

   ----------------------------------
   -- Is_Pragma_Annotate_GNATprove --
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

   --------------------------------
   -- Is_Predicate_Function_Call --
   --------------------------------

   function Is_Predicate_Function_Call (N : Node_Id) return Boolean is
     (Nkind (N) = N_Function_Call
        and then Is_Predicate_Function (Entity (Name (N))));

   --------------------------------------
   -- Is_Predefined_Initialized_Entity --
   --------------------------------------

   function Is_Predefined_Initialized_Entity (E : Entity_Id) return Boolean is
   begin
      --  In general E might not be in SPARK (e.g. if it came from the front
      --  end globals), so we prefer not to risk a precise check and crash
      --  by an accident. Instead, we do a simple and robust check that is
      --  known to be potentially incomplete (e.g. it will not recognize
      --  variables with default initialization).
      if In_Predefined_Unit (E) then
         case Ekind (E) is
            when E_Variable =>
               declare
                  Full_Type : constant Entity_Id :=
                    (if Is_Private_Type (Etype (E))
                     then Full_View (Etype (E))
                     else Etype (E));
               begin
                  return (Is_Scalar_Type (Full_Type)
                          or else Is_Access_Type (Full_Type))
                    and then Present (Expression (Parent (E)));
               end;
            when E_Abstract_State =>
               declare
                  Initializes : constant Dependency_Maps.Map :=
                    Parse_Initializes (Scope (E), Get_Flow_Scope (Scope (E)));
               begin
                  return Initializes.Contains (Direct_Mapping_Id (E));
               end;
            when others =>
               return False;
         end case;
      else
         return False;
      end if;
   end Is_Predefined_Initialized_Entity;

   -------------------------------------
   -- Is_Protected_Component_Or_Discr --
   -------------------------------------

   function Is_Protected_Component_Or_Discr (E : Entity_Id) return Boolean is
   begin
      --  Protected discriminants appear either as E_In_Parameter (in spec of
      --  protected types, e.g. in pragma Priority) or as E_Discriminant
      --  (everywhere else).
      return Ekind (E) in E_Component | E_Discriminant | E_In_Parameter
        and then Ekind (Scope (E)) = E_Protected_Type;
   end Is_Protected_Component_Or_Discr;

   ------------------------------
   -- Is_Quantified_Loop_Param --
   ------------------------------

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean is
   begin
      --  Parent of the scope might be rewritten by inlining for proof, so we
      --  look at the original node.
      return
        Present (Scope (E))
        and then Present (Parent (Scope (E)))
        and then Nkind (Original_Node (Parent (Scope (E))))
                 = N_Quantified_Expression;
   end Is_Quantified_Loop_Param;

   ------------------------------------
   -- Is_Selected_For_Loop_Unrolling --
   ------------------------------------

   function Is_Selected_For_Loop_Unrolling
     (Loop_Stmt : Node_Id) return Boolean
   is
      --  Variables used in loop unrolling
      Low_Val  : Uint;
      High_Val : Uint;
      Unroll   : Unrolling_Type;
   begin
      Candidate_For_Loop_Unrolling (Loop_Stmt   => Loop_Stmt,
                                    Output_Info => False,
                                    Result      => Unroll,
                                    Low_Val     => Low_Val,
                                    High_Val    => High_Val);

      return not Gnat2Why_Args.No_Loop_Unrolling
        and then Unroll /= No_Unrolling;
   end Is_Selected_For_Loop_Unrolling;

   ------------------------
   -- Is_Standard_Entity --
   ------------------------

   function Is_Standard_Entity (E : Entity_Id) return Boolean is
     (for some S of Standard_Entity => S = E);

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

   -------------------------------
   -- May_Issue_Warning_On_Node --
   -------------------------------

   function May_Issue_Warning_On_Node (N : Node_Id) return Boolean is
   begin
      if Instantiation_Location (Sloc (N)) = No_Location then
         declare
            Subp : constant Entity_Id :=
              Unique_Entity
                (Lib.Xref.SPARK_Specific.
                   Enclosing_Subprogram_Or_Library_Package (N));
         begin
            return Present (Subp)
              and then Analysis_Requested (Subp, With_Inlined => False);
         end;
      else
         return False;
      end if;
   end May_Issue_Warning_On_Node;

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

      procedure Count_Assoc is new Traverse_More_Proc (Find_Assoc);

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
      Root     : constant Entity_Id := Root_Retysp (Rec_Type);

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
            --  Only follow the link if the scope of the corresponding
            --  discriminant is in SPARK to avoid hopping outside of the
            --  SPARK bondaries.

            declare
               Par_Discr : constant Entity_Id :=
                 Corresponding_Discriminant (Comp);
            begin

               if Present (Par_Discr)
                 and then Entity_In_SPARK (Retysp (Scope (Par_Discr)))
               then
                  Comp     := Par_Discr;
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
            end;
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

   -------------------
   -- Shape_Of_Node --
   -------------------

   function Shape_Of_Node (Node : Node_Id) return String is

      function Label_Append
        (Buf : Unbounded_String)
         return Unbounded_String
      is
        (if Buf = Null_Unbounded_String
         then Null_Unbounded_String
         else "__" & Buf);

      Buf     : Unbounded_String := Null_Unbounded_String;
      Node_It : Node_Id := Node;

   --  Start of processing for Shape_Of_Node

   begin
      while Present (Node_It) loop
         case Nkind (Node_It) is

         when N_Subprogram_Body
            | N_Subprogram_Specification
            | N_Expression_Function
            | N_Package_Body
            | N_Package_Specification
            | N_Generic_Subprogram_Declaration
         =>
            exit;

         when N_Loop_Statement =>
            declare
               It_Scheme : constant Node_Id := Iteration_Scheme (Node_It);
            begin
               if Present (It_Scheme) then
                  case Nkind (It_Scheme) is
                  when N_Loop_Parameter_Specification |
                       N_Iterator_Specification       =>
                     --  for
                     Buf := "for" & Label_Append (Buf);
                  when others =>
                     --  while
                     Buf := "while" & Label_Append (Buf);
                  end case;
               else
                  --  loop
                  Buf := "loop" & Label_Append (Buf);
               end if;
            end;

            if Identifier (Node_It) /= Empty then
               Buf := Get_Name_String (Chars (Identifier (Node_It)))
                 & "_" & Buf;
            end if;

         when N_Case_Statement
            | N_Case_Expression
         =>
            Buf := "case" & Label_Append (Buf);

         when N_If_Statement
            | N_If_Expression
         =>
            Buf := "if" & Label_Append (Buf);

         when N_Enumeration_Representation_Clause =>
            Buf := Get_Name_String (Chars (Identifier (Node_It)))
              & "_rep" & Label_Append (Buf);

         when N_At_Clause =>
            Buf := Get_Name_String (Chars (Identifier (Node_It)))
              & "_at" & Label_Append (Buf);

         when N_Record_Representation_Clause =>
            Buf := Get_Name_String (Chars (Identifier (Node_It)))
              & "_" & Buf;

         when N_Component_Clause =>
            Buf := Get_Name_String (Chars (Component_Name (Node_It)))
              & "_rep" & Label_Append (Buf);

         when N_Mod_Clause =>
            Buf := "modrep" & Label_Append (Buf);

         when N_Attribute_Definition_Clause =>
            Buf := Get_Name_String (Chars (Name (Node_It))) & "_"
              & Get_Name_String (Chars (Node_It))
              & "_def" & Label_Append (Buf);

         when N_Pragma_Argument_Association =>
            Buf := "pragargs" & Label_Append (Buf);

         when N_Op_Add =>
            Buf := "add" & Label_Append (Buf);

         when N_Op_Concat =>
            Buf := "concat" & Label_Append (Buf);

         when N_Op_Expon =>
            Buf := "exp" & Label_Append (Buf);

         when N_Op_Subtract =>
            Buf := "sub" & Label_Append (Buf);

         when N_Op_Divide =>
            Buf := "div" & Label_Append (Buf);

         when N_Op_Mod =>
            Buf := "mod" & Label_Append (Buf);

         when N_Op_Multiply =>
            Buf := "mult" & Label_Append (Buf);

         when N_Op_Rem =>
            Buf := "rem" & Label_Append (Buf);

         when N_Op_And =>
            Buf := "and" & Label_Append (Buf);

         when N_Op_Compare =>
            Buf := "cmp" & Label_Append (Buf);

         when N_Op_Or =>
            Buf := "or" & Label_Append (Buf);

         when N_Op_Xor =>
            Buf := "xor" & Label_Append (Buf);

         when N_Op_Rotate_Left =>
            Buf := "rol" & Label_Append (Buf);

         when N_Op_Rotate_Right =>
            Buf := "ror" & Label_Append (Buf);

         when N_Op_Shift_Left =>
            Buf := "lsl" & Label_Append (Buf);

         when N_Op_Shift_Right =>
            Buf := "lsr" & Label_Append (Buf);

         when N_Op_Shift_Right_Arithmetic =>
            Buf := "asr" & Label_Append (Buf);

         when N_Op_Abs =>
            Buf := "abs" & Label_Append (Buf);

         when N_Op_Minus =>
            Buf := "minus" & Label_Append (Buf);

         when N_Op_Not =>
            Buf := "not" & Label_Append (Buf);

         when N_Op_Plus =>
            Buf := "plus" & Label_Append (Buf);

         when N_Attribute_Reference =>
            Buf := Get_Name_String (Attribute_Name (Node_It))
              & "_ref" & Label_Append (Buf);

         when N_Membership_Test =>
            Buf := "in" & Label_Append (Buf);

         when N_And_Then =>
            Buf := "andthen" & Label_Append (Buf);

         when N_Or_Else =>
            Buf := "orelse" & Label_Append (Buf);

         when N_Subprogram_Call =>
            Buf := "call_" &
              Get_Name_String (Chars (Get_Called_Entity (Node_It)))
              & Label_Append (Buf);

         when N_Indexed_Component =>
            Buf := "ixdcomp" & Label_Append (Buf);

         when N_Null =>
            Buf := "null" & Label_Append (Buf);

         when N_Qualified_Expression =>
            Buf := Get_Name_String (Chars (Subtype_Mark (Node_It)))
                                    & "_qual" & Label_Append (Buf);

         when N_Quantified_Expression =>
            Buf := (if All_Present (Node_It) then "forall" else "forsome")
              & Label_Append (Buf);

         when N_Aggregate =>
            Buf := "aggr" & Label_Append (Buf);

         when N_Allocator =>
            Buf := "new_" & Buf;

         when N_Raise_Expression =>
            Buf := "raise" & Label_Append (Buf);

         when N_Range =>
            Buf := "range" & Label_Append (Buf);

         when N_Selected_Component =>
            Buf := "selectcomp" & Label_Append (Buf);

         when N_Slice =>
            Buf := "slice" & Label_Append (Buf);

         when N_Type_Conversion | N_Unchecked_Type_Conversion =>
            Buf := "typeconv" & Label_Append (Buf);

         when N_Subtype_Indication =>
            Buf := Get_Name_String (Chars (Subtype_Mark (Node_It)))
              & "_ind" & Label_Append (Buf);

         when N_Formal_Type_Declaration
            | N_Implicit_Label_Declaration
            | N_Object_Declaration
            | N_Formal_Object_Declaration
         =>
            declare
               I_Name : constant Name_Id := Chars (Defining_Identifier
                                                   (Node_It));
               Name_Str : constant String :=
                 (if I_Name /= No_Name and then I_Name /= Error_Name then
                     Get_Name_String (I_Name) & "_"
                  else "");
            begin
               Buf := Name_Str & "decl" & Label_Append (Buf);
            end;

         when N_Full_Type_Declaration
            | N_Incomplete_Type_Declaration
            | N_Protected_Type_Declaration
            | N_Private_Type_Declaration
            | N_Subtype_Declaration
         =>
            Buf := Get_Name_String (Chars (Defining_Identifier (Node_It)))
              & "_def" & Label_Append (Buf);

         when N_Private_Extension_Declaration =>
            Buf := Get_Name_String (Chars (Defining_Identifier (Node_It)))
              & "_priv" & Label_Append (Buf);

         when N_Body_Stub =>
            Buf := Get_Name_String (Chars (Defining_Identifier (Node_It)))
              & "_stub" & Label_Append (Buf);

         when N_Generic_Instantiation =>
            Buf := Get_Name_String (Chars (Defining_Identifier (Node_It)))
              & "_inst" & Label_Append (Buf);

         when N_Array_Type_Definition =>
            Buf := "arrayof_" & Buf;

         when N_Assignment_Statement =>
            declare
               Obj : constant Entity_Id :=
                 Get_Enclosing_Object (Name (Node_It));
               Obj_Name : Name_Id;

            begin
               Buf := "assign" & Label_Append (Buf);

               if Present (Obj) then
                  Obj_Name := Chars (Obj);

                  if Obj_Name /= No_Name and then Obj_Name /= Error_Name then
                     Buf := Get_Name_String (Obj_Name) & "_" & Buf;
                  end if;
               end if;
            end;

         when N_Block_Statement =>
            declare
               Tmp : constant String := (if Identifier (Node_It) /= Empty
                                         then
                                            Get_Name_String
                                           (Chars (Identifier (Node_It))) & "_"
                                         else "");
            begin
               Buf := Tmp & "declblk" & Label_Append (Buf);
            end;

         when N_Goto_Statement =>
            Buf := "goto_" & Get_Name_String (Chars (Name (Node_It)))
              & Label_Append (Buf);

         when N_Raise_Statement =>
            Buf := "raise" & (if Name (Node_It) /= Empty then
                                 "_" & Get_Name_String
                                (Chars (Name (Node_It)))
                              else "") & Label_Append (Buf);

         when N_Simple_Return_Statement
            | N_Extended_Return_Statement
         =>
            Buf := "return" & Label_Append (Buf);

         when N_Exit_Statement =>
            Buf := "exit" & (if Name (Node_It) /= Empty then
                                "_" & Get_Name_String (Chars (Name (Node_It)))
                             else "")
              & Label_Append (Buf);

         when others =>
            null;

         end case;

         Node_It := Parent (Node_It);
      end loop;

      return To_String (Buf);
   end Shape_Of_Node;

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

      --  Local variables

      Name : String := Short_Name (E);
      Loc  : Source_Ptr := Sloc (E);
      Buf  : Source_Buffer_Ptr;

   --  Start of processing for Source_Name

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

      -----------------------
      -- Local Subprograms --
      -----------------------

      function Count_Parentheses (S : String; C : Character) return Natural
        with Pre => C in '(' | ')';
      --  Returns the number of times parenthesis character C should be added
      --  to string S for getting a correctly parenthesized result. For C = '('
      --  this means prepending the character, for C = ')' this means appending
      --  the character.

      function Fix_Parentheses (S : String) return String;
      --  Counts the number of required opening and closing parentheses in S to
      --  respectively prepend and append for getting correct parentheses. Then
      --  returns S with opening parentheses prepended and closing parentheses
      --  appended so that the result is correctly parenthesized.

      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String
      with Pre => Present (Expr);

      function Real_Image_10 (U : Ureal) return String is
        (Real_Image (U, 10));

      function String_Image (S : String_Id) return String is
        ('"' & Get_Name_String (String_To_Name (S)) & '"');

      function Node_To_String is new
        Expression_Image (Real_Image_10, String_Image, Ident_Image);
      --  The actual printing function

      -----------------------
      -- Count_Parentheses --
      -----------------------

      function Count_Parentheses (S : String; C : Character) return Natural is

         procedure Next_Char (Count : in out Natural; C, D, Ch : Character);
         --  Process next character Ch and update the number Count of C
         --  characters to add for correct parenthesizing, where D is the
         --  opposite parenthesis.

         procedure Next_Char (Count : in out Natural; C, D, Ch : Character) is
         begin
            if Ch = D then
               Count := Count + 1;
            elsif Ch = C and then Count > 0 then
               Count := Count - 1;
            end if;
         end Next_Char;

         Count : Natural := 0;

      --  Start of processing for Count_Parentheses

      begin
         if C = '(' then
            for Ch of reverse S loop
               Next_Char (Count, C, ')', Ch);
            end loop;
         else
            for Ch of S loop
               Next_Char (Count, C, '(', Ch);
            end loop;
         end if;

         return Count;
      end Count_Parentheses;

      ---------------------
      -- Fix_Parentheses --
      ---------------------

      function Fix_Parentheses (S : String) return String is
         Count_Open  : constant Natural := Count_Parentheses (S, '(');
         Count_Close : constant Natural := Count_Parentheses (S, ')');
      begin
         return (1 .. Count_Open => '(') & S & (1 .. Count_Close => ')');
      end Fix_Parentheses;

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
         --  For compiler generated identifiers, try to print the original node
         --  instead.

         if not Comes_From_Source (Expr)
           and then Is_Rewrite_Substitution (Expr)
         then
            return Node_To_String (Original_Node (Expr), "");
         end if;

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
      return Fix_Parentheses (Node_To_String (N, ""));
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
      if Ekind (E) in E_Abstract_State | E_Variable then
         declare
            Encapsulating : constant Entity_Id := Encapsulating_State (E);

         begin
            return Present (Encapsulating)
              and then Is_Single_Concurrent_Object (Encapsulating);
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
      if Ekind (E) in E_Abstract_State | E_Variable then
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

   -----------------------------
   -- Unique_Main_Unit_Entity --
   -----------------------------

   function Unique_Main_Unit_Entity return Entity_Id is
   begin
      --  Main_Unit_Entity is not reliable, e.g. for instance-as-a-unit its
      --  Ekind is E_Void; Cunit_Entity (Main_Unit) is more reliable, but
      --  might point to the body entity, so Unique_Entity is required.

      return Unique_Entity (Cunit_Entity (Main_Unit));
   end Unique_Main_Unit_Entity;

end SPARK_Util;
