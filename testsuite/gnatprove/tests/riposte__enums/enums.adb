package body Enums
is
   type Big_Type is (Elem_0, Elem_1, Elem_2,
                     Elem_3, Elem_4, Elem_5,
                     Elem_6, Elem_7, Elem_8);

   subtype Smaller_Type is Big_Type range Elem_3 .. Elem_5;

   function Enum_Equals (A, B : in Big_Type) return Boolean
     with Post => Enum_Equals'Result = (A = B)  --  @POSTCONDITION:PASS
   is
   begin
      return A = B;
   end Enum_Equals;

   function Enum_Equals_Broken_A (A, B : in Big_Type) return Boolean
     with Depends => (Enum_Equals_Broken_A'Result => A,
                      null => B),
          Post    => Enum_Equals_Broken_A'Result = (A = B)  --  @POSTCONDITION:FAIL
   is
      Tmp : Big_Type := A;
   begin
      return Tmp = A;
   end Enum_Equals_Broken_A;

   function Enum_Equals_Broken_B (A, B : in Big_Type) return Boolean
     with Post => Enum_Equals_Broken_B'Result = (A = B)  --  @POSTCONDITION:FAIL
   is
   begin
      return A <= B;
   end Enum_Equals_Broken_B;

   function Enum_Equals_Subtype (A : in Big_Type;
                                 B : in Smaller_Type)
                                return Boolean
     with Post => Enum_Equals_Subtype'Result = (A = B)  --  @POSTCONDITION:PASS
   is
   begin
      return A = B;
   end Enum_Equals_Subtype;

   function Enum_LT_5 (A : in Big_Type) return Boolean
     with Post => Enum_LT_5'Result = (A < Elem_5)  --  @POSTCONDITION:PASS
   is
      R : Boolean;
   begin
      case A is
         when Elem_0 =>
            R := True;
         when Elem_1 =>
            R := True;
         when Elem_2 =>
            R := (A = Elem_2);
         when Elem_3 =>
            R := (A /= Big_Type'Last);
         when Elem_4 =>
            R := (A < Elem_6);
         when Elem_7 =>
            R := (A < Elem_5);
         when others =>
            R := False;
      end case;
      return R;
   end Enum_LT_5;

   function Enum_LT_5_Broken_A (A : in Big_Type) return Boolean
     with Post => Enum_LT_5_Broken_A'Result = (A < Elem_5)  --  @POSTCONDITION:FAIL
   is
      R : Boolean;
   begin
      case A is
         when Elem_0 =>
            R := True;
         when Elem_2 =>
            R := (A = Elem_2);
         when Elem_3 =>
            R := (A /= Big_Type'Last);
         when Elem_4 =>
            R := (A < Elem_6);
         when Elem_7 =>
            R := (A <= A);
         when others =>
            R := A < A;
      end case;
      return R;
   end Enum_LT_5_Broken_A;

   function Is_Subenum (A : in Big_Type) return Boolean
     with Post => Is_Subenum'Result = (A in Smaller_Type)  --  @POSTCONDITION:PASS
   is
      R : Boolean;
   begin
      if A >= Smaller_Type'First then
         if A <= Smaller_Type'Last then
            R := True;
         else
            R := False;
         end if;
      else
         R := False;
      end if;
      return R;
   end Is_Subenum;

   function Tick_Pos (A : in Big_Type) return Integer
     with Post => Big_Type'Val (Tick_Pos'Result) = A  --  @POSTCONDITION:PASS
   is
      R : Integer;
   begin
      case A is
         when Elem_0 =>
            R := 0;
         when Elem_1 =>
            R := Big_Type'Pos (A);
         when Elem_2 =>
            R := Big_Type'Pos (Elem_2);
         when Elem_3 =>
            R := 1 + (1 + 1);
         when Elem_4 =>
            if A in Smaller_Type then
               R := 4;
            else
               R := 0;
            end if;
         when Elem_5 =>
            R := Big_Type'Pos (Smaller_Type'First) + 2;
         when Elem_6 =>
            if A in Smaller_Type then
               R := 0;
            else
               R := 6;
            end if;
         when Elem_8 =>
            R := Big_Type'Pos (Big_Type'Last);
         when others =>
            R := 7;
      end case;
      return R;
   end Tick_Pos;

   procedure Integer_To_Smaller_Type (I       : in     Integer;
                                      Result  :    out Smaller_Type;
                                      Success :    out Boolean)
     with Depends => ((Result, Success) => I),
          Post    => (if Success then Result = Smaller_Type'Val (I))  --  @POSTCONDITION:PASS
   is
   begin
      if I >= Smaller_Type'Pos (Smaller_Type'First) and
        I <= Smaller_Type'Pos (Smaller_Type'Last)
      then
         Success := True;
         Result  := Smaller_Type'Val (I);
      else
         Success := False;
         Result  := Smaller_Type'First;
      end if;
   end Integer_To_Smaller_Type;

   function Next_A (A : in Smaller_Type) return Smaller_Type
     with Post => (if A = Elem_3 then Next_A'Result = Elem_4)  --  @POSTCONDITION:PASS
                     and (if A = Elem_4 then Next_A'Result = Elem_5)
                     and (if A = Elem_5 then Next_A'Result = Elem_3)
   is
      R : Smaller_Type;
   begin
      if A < Smaller_Type'Last then
         R := Smaller_Type'Succ (A);
      else
         R := Smaller_Type'First;
      end if;
      return R;
   end Next_A;

   function Next_B (A : in Smaller_Type) return Smaller_Type
     with Post => (if A < Smaller_Type'Last then Next_B'Result =  --  @POSTCONDITION:PASS
                                                   Smaller_Type'Succ (A))
                     and (if A = Smaller_Type'Last then Next_B'Result =
                                                          Smaller_Type'First)
   is
      R : Smaller_Type;
   begin
      case A is
         when Elem_3 => R := Elem_4;
         when Elem_4 => R := Elem_5;
         when Elem_5 => R := Elem_3;
      end case;
      return R;
   end Next_B;

   function Succ_A (A : in Big_Type) return Big_Type
     with Post => Succ_A'Result = Big_Type'Succ (A)
   is
   begin
      return Big_Type'Succ (A);  --  @RANGE_CHECK:FAIL
   end Succ_A;

   function Subtypes_Broken (X : in Smaller_Type) return Big_Type
   is
      type R is record
         F : Smaller_Type;
      end record;

      Tmp : R;
   begin
      Tmp := R'(F => X);
      return Tmp.F;
   end Subtypes_Broken;

end Enums;
