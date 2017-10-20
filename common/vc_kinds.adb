------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

package body VC_Kinds is

   function To_JSON (S : Prover_Stat) return JSON_Value;
   function To_JSON (L : Cntexample_Lines) return JSON_Value;
   function To_JSON (C : Cntexample_Elt) return JSON_Value;
   function To_JSON (L : Cntexample_Elt_Lists.List) return JSON_Value;
   function To_JSON (K : CEE_Kind) return JSON_Value;

   function From_JSON (V : JSON_Value) return Cntexample_Lines;
   function From_JSON (V : JSON_Value) return Cntexample_Elt;
   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List;
   function From_JSON (V : JSON_Value) return CEE_Kind;
   function From_JSON (V : JSON_Value) return Cntexmp_Type;

   function Get_Typed_Cntexmp_Value (V : JSON_Value) return Cntexmp_Value;

   -----------------
   -- CWE_Message --
   -----------------

   function CWE_Message (Kind : VC_Kind) return String is
      CWE_Id : constant String :=
        (case Kind is
         --  CWE-369: Divide By Zero

         when VC_Division_Check            => "369",

         --  CWE-120: Buffer Copy without Checking Size of Input ('Classic
         --  Buffer Overflow')

         when VC_Index_Check               => "120",

         --  CWE-190: Integer Overflow or Wraparound

         when VC_Overflow_Check            => "190",

         --  CWE-739: CWE CATEGORY: CERT C Secure Coding Section 05 - Floating
         --  Point (FLP)

         when VC_FP_Overflow_Check         => "739",

         --  CWE-682: Incorrect Calculation

         when VC_Range_Check
            | VC_Predicate_Check
            | VC_Predicate_Check_On_Default_Value => "682",

         --  CWE-136: CWE CATEGORY: Type Errors

         when VC_Discriminant_Check
            | VC_Tag_Check                 => "136",

         --  CWE-835: Loop with Unreachable Exit Condition ('Infinite Loop')

         when VC_Loop_Variant              => "835",

         --  We did not find a relevant CWE for the following yet

         when VC_Invariant_Check
            | VC_Invariant_Check_On_Default_Value
            | VC_Length_Check
            | VC_Ceiling_Interrupt
            | VC_Interrupt_Reserved
            | VC_Ceiling_Priority_Protocol
            | VC_Task_Termination
            | VC_Initial_Condition
            | VC_Default_Initial_Condition
            | VC_Precondition
            | VC_Precondition_Main
            | VC_Postcondition
            | VC_Refined_Post
            | VC_Contract_Case
            | VC_Disjoint_Contract_Cases
            | VC_Complete_Contract_Cases
            | VC_Loop_Invariant
            | VC_Loop_Invariant_Init
            | VC_Loop_Invariant_Preserv
            | VC_Assert
            | VC_Raise
            | VC_Weaker_Pre
            | VC_Trivial_Weaker_Pre
            | VC_Stronger_Post
            | VC_Weaker_Classwide_Pre
            | VC_Stronger_Classwide_Post   => "");
   begin
      if CWE_Id = "" then
         return "";
      else
         return " [CWE " & CWE_Id & "]";
      end if;
   end CWE_Message;

   function CWE_Message (Kind : Flow_Tag_Kind) return String is
      CWE_Id : constant String :=
        (case Kind is
         --  CWE-561: Dead Code

         when Dead_Code                     => "561",

         --  CWE-457: Use of Uninitialized Variable

         when Default_Initialization_Mismatch
            | Uninitialized                 => "457",

         --  CWE-563: Assignment to Variable without Use ('Unused Variable')

         when Unused
            | Unused_Initial_Value          => "563",

         when Empty_Tag
            | Aliasing
            | Depends_Null
            | Depends_Missing
            | Depends_Missing_Clause
            | Depends_Wrong
            | Global_Missing
            | Global_Wrong
            | Export_Depends_On_Proof_In
            | Hidden_Unexposed_State
            | Illegal_Update
            | Impossible_To_Initialize_State
            | Ineffective
            | Initializes_Wrong
            | Inout_Only_Read
            | Missing_Return
            | Not_Constant_After_Elaboration
            | Pragma_Elaborate_All_Needed
            | Pragma_Elaborate_Body_Needed
            | Refined_State_Wrong
            | Side_Effects
            | Stable
            | Non_Volatile_Function_With_Volatile_Effects
            | Volatile_Function_Without_Volatile_Effects
            | Reference_To_Non_CAE_Variable => "");
   begin
      if CWE_Id = "" then
         return "";
      else
         return " [CWE " & CWE_Id & "]";
      end if;
   end CWE_Message;

   ---------------
   -- From_JSON --
   ---------------

   function From_JSON (V : JSON_Value) return Prover_Stat is
   begin
      return Prover_Stat'(Count     => Get (Get (V, "count")),
                          Max_Steps => Get (Get (V, "max_steps")),
                          Max_Time  => Get (Get (V, "max_time")));
   end From_JSON;

   function From_JSON (V : JSON_Value) return Prover_Stat_Maps.Map is

      Map : Prover_Stat_Maps.Map;

      procedure Process_Prover_Stat (Name : UTF8_String; Value : JSON_Value);

      -------------------------
      -- Process_Prover_Stat --
      -------------------------

      procedure Process_Prover_Stat (Name : UTF8_String; Value : JSON_Value) is
      begin
         Map.Insert (Name, From_JSON (Value));
      end Process_Prover_Stat;

   --  Start of processing for From_Json

   begin
      Map_JSON_Object (V, Process_Prover_Stat'Access);
      return Map;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Prover_Category is
      S : constant String := Get (V);
   begin
      if S = "codepeer" then
         return PC_Codepeer;
      elsif S = "interval" then
         return PC_Interval;
      elsif S = "prover" then
         return PC_Prover;
      elsif S = "flow" then
         return PC_Flow;
      end if;
      raise Program_Error;
   end From_JSON;

   function From_JSON (V : JSON_Value) return CEE_Kind is
      S : constant String := Get (V);
   begin
      if S = "variable" then
         return CEE_Variable;
      elsif S = "error_message" then
         return CEE_Error_Msg;
      elsif S = "old" then
         return CEE_Old;
      elsif S = "result" then
         return CEE_Result;
      elsif S = "other" then
         return CEE_Other;
      end if;
      raise Program_Error;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_File_Maps.Map is

      Map : Cntexample_File_Maps.Map;

      procedure Process_Entry (Name : UTF8_String; Value : JSON_Value);

      -------------------
      -- Process_Entry --
      -------------------

      procedure Process_Entry (Name : UTF8_String; Value : JSON_Value) is
      begin
         Map.Insert (Name, From_JSON (Value));
      end Process_Entry;

   --  Start of processing for From_JSON

   begin
      Map_JSON_Object (V, Process_Entry'Access);
      return Map;
   end From_JSON;

   function From_JSON (V : JSON_Value) return  Cntexample_Lines is
      Res : Cntexample_Lines :=
        Cntexample_Lines'(VC_Line =>
                             (if Has_Field (V, "vc_line")
                              then From_JSON ((Get (V, "vc_line")))
                              else Cntexample_Elt_Lists.Empty_List),
                           Other_Lines => Cntexample_Line_Maps.Empty_Map);

      procedure Process_Entry (Name : UTF8_String; Value : JSON_Value);

      -------------------
      -- Process_Entry --
      -------------------

      procedure Process_Entry (Name : UTF8_String; Value : JSON_Value) is
      begin
         if Name /= "vc_line" then
            Res.Other_Lines.Insert
              (Natural'Value (Name), From_JSON (Value));
         end if;
      end Process_Entry;

   --  Start of processing for From_JSON

   begin
      Map_JSON_Object (V, Process_Entry'Access);
      return Res;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexmp_Type is
      pragma Assert (Has_Field (V, "type"));
      T : constant String := Get (V, "type");
      E : constant Unbounded_String := To_Unbounded_String (T);
   begin

      if E = "Integer" then
         return Cnt_Integer;
      end if;

      if E = "Decimal" then
         return Cnt_Decimal;
      end if;

      if E = "Float" then
         return Cnt_Float;
      end if;

      if E = "Boolean" then
         return Cnt_Boolean;
      end if;

      if E = "Bv" then
         return Cnt_Bitvector;
      end if;

      if E = "Unparsed" then
         return Cnt_Unparsed;
      end if;

      if E = "Array" then
         return Cnt_Array;
      end if;

      if E = "Record" then
         return Cnt_Record;
      end if;

      return Cnt_Invalid;
   end From_JSON;

   -----------------------------
   -- Get_Typed_Cntexmp_Value --
   -----------------------------

   function Get_Typed_Cntexmp_Value (V : JSON_Value) return Cntexmp_Value is
      T : constant Cntexmp_Type := From_JSON (V);
   begin
      case T is
         when Cnt_Integer   =>
            return (T => Cnt_Integer,
                    I => Get (V, "val"));

         when Cnt_Decimal   =>
            return (T => Cnt_Decimal,
                    D => Get (V, "val"));

         --  Float values are complex so they are sent as JSON records. Example
         --  of values are infinities, zeroes, etc
         when Cnt_Float     =>
            declare
               Val        : constant JSON_Value := Get (V, "val");
               Float_Type : constant String := Get (Val, "cons");
            begin
               if Float_Type = "Plus_infinity" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_Plus_Infinity));

               elsif Float_Type = "Minus_infinity" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_Minus_Infinity));

               elsif Float_Type = "Plus_zero" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_Plus_Zero));

               elsif Float_Type = "Minus_zero" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_Minus_Zero));

               elsif Float_Type = "Not_a_number" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type => Float_NaN));

               elsif Float_Type = "Float_value" then
                  return (T => Cnt_Float,
                          F =>
                             new Float_Value'(F_Type        => Float_Val,
                                              F_Sign        =>
                                                Get (Val, "sign"),
                                              F_Exponent    =>
                                                Get (Val, "exponent"),
                                              F_Significand =>
                                                Get (Val, "significand")));

               else
                  return (T => Cnt_Invalid,
                          S => Null_Unbounded_String);
               end if;
            end;

         when Cnt_Boolean   =>
            return (T  => Cnt_Boolean,
                    Bo => Get (V, "val"));

         when Cnt_Bitvector =>
            return (T => Cnt_Bitvector,
                    B => Get (V, "val"));

         when Cnt_Unparsed  =>
            return (T => Cnt_Unparsed,
                    U => Get (V, "val"));

         when Cnt_Record    =>
            declare
               Record_Val : constant JSON_Value := Get (V, "val");
               Field_Value_List : Cntexmp_Value_Array.Map;
               Discr_Value_List : Cntexmp_Value_Array.Map;
               JS_Array_Discr   : constant JSON_Array :=
                                    Get (Record_Val, "Discr");
               JS_Array_Field   : constant JSON_Array :=
                                    Get (Record_Val, "Field");

            begin

               for Index in 1 .. Length (JS_Array_Discr) loop
                  declare
                     Json_Element : constant JSON_Value :=
                                      Get (JS_Array_Discr, Index);
                     Elem_Ptr     : constant Cntexmp_Value_Ptr :=
                                      new Cntexmp_Value'(
                                       Get_Typed_Cntexmp_Value (Json_Element));
                  begin
                     Discr_Value_List.Insert (Index'Image, Elem_Ptr);
                  end;
               end loop;

               for Index in 1 .. Length (JS_Array_Field) loop
                  declare
                     Json_Element : constant JSON_Value :=
                                      Get (JS_Array_Field, Index);
                     Elem_Ptr     : constant Cntexmp_Value_Ptr :=
                                      new Cntexmp_Value'(
                                       Get_Typed_Cntexmp_Value (Json_Element));
                  begin
                     Field_Value_List.Insert (Index'Image, Elem_Ptr);
                  end;
               end loop;
               return (T  => Cnt_Record,
                       Fi => Field_Value_List,
                       Di => Discr_Value_List);
            end;

         when Cnt_Array     =>
            declare
               JS_Array     : constant JSON_Array := Get (V, "val");
               Indice_Array : Cntexmp_Value_Array.Map;
               Other_Ptr    : Cntexmp_Value_Ptr := null;

            begin
               for Index in 1 .. Length (JS_Array) loop
                  declare
                     Json_Element : constant JSON_Value :=
                       Get (JS_Array, Index);

                  begin
                     if Has_Field (Json_Element, "others") then
                        declare
                           V : constant JSON_Value :=
                             Get (Json_Element, "others");
                        begin
                           pragma Assert (Other_Ptr = null);
                           Other_Ptr := new Cntexmp_Value'(
                                              Get_Typed_Cntexmp_Value (V));
                        end;
                     else
                        declare
                           Indice   : constant String :=
                                        Get (Json_Element, "indice");
                           Elem_Ptr : constant Cntexmp_Value_Ptr :=
                                        new Cntexmp_Value'(
                                          Get_Typed_Cntexmp_Value
                                            (Get (Json_Element, "value")));
                        begin
                           Cntexmp_Value_Array.Insert
                             (Indice_Array, Indice, Elem_Ptr);
                        end;
                     end if;

                  end;
               end loop;
               if Other_Ptr = null then
                  Other_Ptr :=
                    new Cntexmp_Value'(T => Cnt_Invalid,
                                       S => Null_Unbounded_String);

               end if;
               return (T             => Cnt_Array,
                       Array_Indices => Indice_Array,
                       Array_Others  => Other_Ptr);
            end;

         when Cnt_Invalid =>
            return (T => Cnt_Invalid,
                    S => Null_Unbounded_String);
      end case;
   end Get_Typed_Cntexmp_Value;

   function From_JSON (V : JSON_Value) return Cntexample_Elt is
      Cnt_Value : constant Cntexmp_Value_Ptr :=
        new Cntexmp_Value'(Get_Typed_Cntexmp_Value (Get (V, "value")));
   begin
      return
        Cntexample_Elt'(Kind        => From_JSON (Get (V, "kind")),
                        Name        => Get (Get (V, "name")),
                        Value       => Cnt_Value,
                        Val_Str     => Null_Unbounded_String);
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List is
      Res : Cntexample_Elt_Lists.List := Cntexample_Elt_Lists.Empty_List;
      Ar  : constant JSON_Array       := Get (V);
   begin
      for Var_Index in Positive range 1 .. Length (Ar) loop
         declare
            Elt : constant JSON_Value := Get (Ar, Var_Index);
         begin
            Res.Append (From_JSON (Elt));
         end;
      end loop;
      return Res;
   end From_JSON;

   -------------
   -- To_JSON --
   -------------

   function To_JSON (S : Prover_Stat) return JSON_Value is
      C : constant JSON_Value := Create_Object;
   begin
      Set_Field (C, "count", S.Count);
      Set_Field (C, "max_steps", S.Max_Steps);
      Set_Field (C, "max_time", S.Max_Time);
      return C;
   end To_JSON;

   function To_JSON (M : Prover_Stat_Maps.Map) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      for C in M.Iterate loop
         Set_Field (Obj, Prover_Stat_Maps.Key (C), To_JSON (M (C)));
      end loop;
      return Obj;
   end To_JSON;

   function To_JSON (P : Prover_Category) return JSON_Value is
      S : constant String :=
        (case P is
            when PC_Prover   => "prover",
            when PC_Interval => "interval",
            when PC_Codepeer => "codepeer",
            when PC_Flow     => "flow");
   begin
      return Create (S);
   end To_JSON;

   function To_JSON (K : CEE_Kind) return JSON_Value is
      S : constant String :=
        (case K is
            when CEE_Old       => "old",
            when CEE_Result    => "result",
            when CEE_Variable  => "variable",
            when CEE_Error_Msg => "error_message",
            when CEE_Other     => "other");
   begin
      return Create (S);
   end To_JSON;

   function To_JSON (F : Cntexample_File_Maps.Map) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      for C in F.Iterate loop
         Set_Field (Obj, Cntexample_File_Maps.Key (C), To_JSON (F (C)));
      end loop;
      return Obj;
   end To_JSON;

   function To_JSON (L : Cntexample_Lines) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;

      function Line_Number_Image (L : Natural) return String;

      -----------------------
      -- Line_Number_Image --
      -----------------------

      function Line_Number_Image (L : Natural) return String is
         S : constant String := Natural'Image (L);
      begin
         return S (S'First + 1 .. S'Last);
      end Line_Number_Image;

   --  Start of processing for To_JSON

   begin
      for C in L.Other_Lines.Iterate loop
         Set_Field (Obj,
                    Line_Number_Image (Cntexample_Line_Maps.Key (C)),
                    To_JSON (L.Other_Lines (C)));
      end loop;
      if not L.VC_Line.Is_Empty then
         Set_Field (Obj, "vc_line", To_JSON (L.VC_Line));
      end if;
      return Obj;
   end To_JSON;

   function To_JSON (C : Cntexample_Elt) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      Set_Field (Obj, "name", C.Name);
      Set_Field (Obj, "value", C.Val_Str);
      Set_Field (Obj, "kind", To_JSON (C.Kind));
      return Obj;
   end To_JSON;

   function To_JSON (L : Cntexample_Elt_Lists.List) return JSON_Value is
      Result : JSON_Array := Empty_Array;
   begin
      for Elt of L loop
         Append (Result, To_JSON (Elt));
      end loop;
      return Create (Result);
   end To_JSON;

   ---------------
   -- To_String --
   ---------------

   function To_String (P : Prover_Category) return String is
   begin
      return (case P is
                 when PC_Prover   => "Automatic provers",
                 when PC_Interval => "Interval",
                 when PC_Codepeer => "CodePeer",
                 when PC_Flow     => "Flow analysis");
   end To_String;

end VC_Kinds;
