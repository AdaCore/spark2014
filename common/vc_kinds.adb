------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
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

   function From_JSON (V : JSON_Value) return  Cntexample_Lines;
   function From_JSON (V : JSON_Value) return Cntexample_Elt;
   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List;
   function From_JSON (V : JSON_Value) return CEE_Kind;

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

      --  Begin processing of From_Json

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
              (Logical_Line_Number'Value (Name), From_JSON (Value));
         end if;
      end Process_Entry;

   begin
      Map_JSON_Object (V, Process_Entry'Access);
      return Res;
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Elt is
   begin
      return
        Cntexample_Elt'(Kind  => From_JSON (Get (V, "kind")),
                        Name  => Get (Get (V, "name")),
                        Value => Get (Get (V, "value")));
   end From_JSON;

   function From_JSON (V : JSON_Value) return Cntexample_Elt_Lists.List is
      Res : Cntexample_Elt_Lists.List := Cntexample_Elt_Lists.Empty_List;
      Ar : constant JSON_Array := Get (V);
   begin
      for Var_Index in Positive range 1 .. Length (Ar) loop
         Res.Append (From_JSON (Get (Ar, Var_Index)));
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
            when CEE_Old => "old",
            when CEE_Result => "result",
            when CEE_Variable => "variable",
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

      function Line_Number_Image (L : Logical_Line_Number) return String;

      -----------------------
      -- Line_Number_Image --
      -----------------------

      function Line_Number_Image (L : Logical_Line_Number) return String is
         S : constant String := Logical_Line_Number'Image (L);
      begin
         return S (S'First + 1 .. S'Last);
      end Line_Number_Image;

      --  begin processing of To_JSON

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
      Set_Field (Obj, "value", C.Value);
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
