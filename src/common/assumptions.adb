------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           A S S U M P T I O N S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

package body Assumptions is

   function Read_Token (V : JSON_Value) return Token;
   function To_JSON (T : Token) return JSON_Value;
   function To_JSON (R : Rule) return JSON_Value;

   ---------------
   -- From_JSON --
   ---------------

   function From_JSON (S : String) return Rule_Lists.List is
      V : constant JSON_Array := Get (Read (S));
   begin
      return From_JSON (V);
   end From_JSON;

   function From_JSON (S : JSON_Array) return Rule_Lists.List is
      Result : Rule_Lists.List := Rule_Lists.Empty_List;
   begin
      for Rule_Index in 1 .. Length (S) loop
         declare
            V           : constant JSON_Value := Get (S, Rule_Index);
            Assumptions : Token_Sets.Set := Token_Sets.Empty_Set;
            JSON_Assume : constant JSON_Array := Get (Get (V, "assumptions"));
         begin
            for A_Index in 1 .. Length (JSON_Assume) loop
               Assumptions.Include (Read_Token (Get (JSON_Assume, A_Index)));
            end loop;
            Result.Append
              (New_Item => (Claim       => Read_Token (Get (V, "claim")),
                            Assumptions => Assumptions));
         end;
      end loop;
      return Result;
   end From_JSON;

   ----------------
   -- Read_Token --
   ----------------

   function Read_Token (V : JSON_Value) return Token is
   begin
      return
        (Predicate => Claim_Kind'Value (Get (Get (V, "predicate"))),
         Arg       => From_JSON (Get (V, "arg")));
   end Read_Token;

   -------------
   -- To_JSON --
   -------------

   function To_JSON (L : Rule_Lists.List) return JSON_Value is
      A : JSON_Array := Empty_Array;
   begin
      for R of L loop
         Append (A, To_JSON (R));
      end loop;
      return Create (A);
   end To_JSON;

   function To_JSON (R : Rule) return JSON_Value is
      Obj   : constant JSON_Value := Create_Object;
      Assum : JSON_Array := Empty_Array;
   begin
      for T of R.Assumptions loop
         Append (Assum, To_JSON (T));
      end loop;
      Set_Field (Obj, "assumptions", Create (Assum));
      Set_Field (Obj, "claim", To_JSON (R.Claim));
      return Obj;
   end To_JSON;

   function To_JSON (T : Token) return JSON_Value is
      Obj : constant JSON_Value := Create_Object;
   begin
      Set_Field (Obj, "predicate", Claim_Kind'Image (T.Predicate));
      Set_Field (Obj, "arg", To_JSON (T.Arg));
      return Obj;
   end To_JSON;

   ---------------
   -- To_String --
   ---------------

   function To_String (T : Token) return String is

      function Human_Readable (C : Claim_Kind) return String;
      --  Human-readable string for claim kind

      --------------------
      -- Human_Readable --
      --------------------

      function Human_Readable (C : Claim_Kind) return String is
      begin
         case C is
            when Claim_Init    =>
               return "initializiation of all out parameters and out Globals";
            when Claim_Pre     =>
               return "the precondition";
            when Claim_Post    =>
               return "the postcondition";
            when Claim_Effects =>
               return "effects on parameters and Global variables";
            when Claim_AoRTE   =>
               return "absence of run-time errors";
         end case;
      end Human_Readable;

   --  Start of processing for To_String

   begin
      return Human_Readable (T.Predicate) & " of " & Subp_Name (T.Arg);
   end To_String;

end Assumptions;
