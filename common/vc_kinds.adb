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

   procedure Get_Typed_Cntexmp_Value (V      : JSON_Value;
                                      Result : out Cntexmp_Value_Ptr);

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

   procedure Get_Typed_Cntexmp_Value (V      : JSON_Value;
                                      Result : out Cntexmp_Value_Ptr) is
      T : constant Cntexmp_Type := From_JSON (V);
   begin
      case T is
         when Cnt_Integer   =>
            Result := new Cntexmp_Value'(T => Cnt_Integer,
                                         I => Get (V, "val"));

         when Cnt_Float     =>
            Result := new Cntexmp_Value'(T => Cnt_Float,
                                         F => Get (V, "val"));

         when Cnt_Boolean   =>
            Result := new Cntexmp_Value'(T  => Cnt_Boolean,
                                         Bo => Get (V, "val"));

         when Cnt_Bitvector =>
            Result := new Cntexmp_Value'(T => Cnt_Bitvector,
                                         B => Get (V, "val"));

         when Cnt_Unparsed  =>
            Result := new Cntexmp_Value'(T => Cnt_Unparsed,
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
                     Elem_Ptr     : Cntexmp_Value_Ptr;
                  begin
                     Get_Typed_Cntexmp_Value (Json_Element, Elem_Ptr);
                     Discr_Value_List.Insert (Index'Image, Elem_Ptr);
                  end;
               end loop;

               for Index in 1 .. Length (JS_Array_Field) loop
                  declare
                     Json_Element : constant JSON_Value :=
                                      Get (JS_Array_Field, Index);
                     Elem_Ptr     : Cntexmp_Value_Ptr;
                  begin
                     Get_Typed_Cntexmp_Value (Json_Element, Elem_Ptr);
                     Field_Value_List.Insert (Index'Image, Elem_Ptr);
                  end;
               end loop;
               Result := new Cntexmp_Value'(T  => Cnt_Record,
                                            Fi => Field_Value_List,
                                            Di => Discr_Value_List);
            end;

         when Cnt_Array     =>
            declare
               JS_Array     : constant JSON_Array := Get (V, "val");
               Indice_Array : Cntexmp_Value_Array.Map;
               Other_Ptr    : Cntexmp_Value_Ptr := new Cntexmp_Value;

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
                           Get_Typed_Cntexmp_Value (V, Other_Ptr);
                        end;
                     else
                        declare
                           Indice   : constant String :=
                                        Get (Json_Element, "indice");
                           Elem_Ptr : Cntexmp_Value_Ptr :=
                                        new Cntexmp_Value;
                        begin
                           Get_Typed_Cntexmp_Value
                             (Get (Json_Element, "value"), Elem_Ptr);
                           Cntexmp_Value_Array.Insert
                             (Indice_Array, Indice, Elem_Ptr);
                        end;
                     end if;

                  end;
               end loop;
               Result := new Cntexmp_Value'(T             => Cnt_Array,
                                            Array_Indices => Indice_Array,
                                            Array_Others  => Other_Ptr);
            end;

         when Cnt_Invalid => Result.all := (T => Cnt_Invalid,
                                            S => Null_Unbounded_String);
      end case;
   end Get_Typed_Cntexmp_Value;

   function From_JSON (V : JSON_Value) return Cntexample_Elt is
      Cnt_Value : Cntexmp_Value_Ptr;
   begin
      Get_Typed_Cntexmp_Value (Get (V, "value"), Cnt_Value);
      return
        Cntexample_Elt'(Kind        => From_JSON (Get (V, "kind")),
                        Name        => Get (Get (V, "name")),
                        Value       => Cnt_Value,
                        Val_Str     => Null_Unbounded_String);
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List is
      Res : Cntexample_Elt_Lists.List := Cntexample_Elt_Lists.Empty_List;
      Ar  : constant JSON_Array     := Get (V);
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
