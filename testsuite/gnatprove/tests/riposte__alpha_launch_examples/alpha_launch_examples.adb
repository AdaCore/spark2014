package body Alpha_Launch_Examples
is
   type U64 is mod 2 ** 64;
   type Enum_T is (Foo, Bar, Baz, Wibble, Bork);
   type Row_T is array (Enum_T) of Enum_T;

   type Rec_T is record
      A : Integer;
      B : Integer;
      C : Integer;
   end record;

   type Scale            is range 0 .. 100;
   type Display_Quantity is range 0 .. 1000;

   function Example_1 (X : in Integer) return Integer
     with Post => Example_1'Result = abs (X)
   is
   begin
      return abs (X);  --  @OVERFLOW_CHECK:FAIL
   end Example_1;

   procedure Example_2 (R : in out Rec_T)
     with Depends => (R => R),
          Post    => R = R'Old'Update (A => R'Old.C,  --  @POSTCONDITION:FAIL
                                       C => R'Old.A)
                       and R /= R'Old
   is
      Tmp : Integer;
   begin
      Tmp := R.A;
      R.A := R.C;
      R.C := Tmp;
   end Example_2;

   function Example_3 (A : in U64;
                       B : in U64)
                      return U64
     with Pre  => A > 17 and B > 19,
          Post => Example_3'Result > 0  --  @POSTCONDITION:FAIL
   is
   begin
      return 73 xor (A * B);
   end Example_3;

   function Example_5 (A      : in Row_T;
                       V1, V2 : in Enum_T)
                      return Boolean
     with Depends => (Example_5'Result => (V1, V2),
                      null => A),
          Pre     =>
            (for all I in Enum_T range Enum_T'First ..
                                         Enum_T'Pred (Enum_T'Last) =>
               (for all J in Enum_T range Enum_T'Succ (I) .. Enum_T'Last =>
                  (A (I) /= A (J)))),
          Post    => Example_5'Result = (A (V1) = A (V2))  --  @POSTCONDITION:FAIL
   is
   begin
      return V1 = V2;
   end Example_5;

   procedure Example_4 (A, B : in out U64)
     with Depends => (A =>+ B,
                      B =>+ A),
          Post    => A = B'Old and B = A'Old
   is
   begin
      A := A xor B;
      B := A xor B;
      A := A xor B;
   end Example_4;

   function Example_6 (A : in Scale)
                      return Display_Quantity
     with Pre =>
       Display_Quantity'Last / Display_Quantity (A) <  --  @DIVISION_CHECK:FAIL
         Display_Quantity'Last
   is
   begin
      return Display_Quantity'Last / Display_Quantity (A);  --  @DIVISION_CHECK:FAIL @OVERFLOW_CHECK:FAIL @RANGE_CHECK:FAIL
   end Example_6;

   function Example_7 (X : in Integer) return Integer
     with Post => 73 rem Example_7'Result /= 42  --  @DIVISION_CHECK:FAIL
   is
      R : Integer;
   begin
      if X = Integer'First then
         R := 73;
      else
         R := abs (X);
      end if;

      return R;
   end Example_7;

end Alpha_Launch_Examples;
