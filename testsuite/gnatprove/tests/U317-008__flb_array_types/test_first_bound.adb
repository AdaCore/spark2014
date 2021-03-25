procedure Test_First_Bound with SPARK_Mode is
   procedure Test_1 with Global => null is
      type My_Mod is mod 15;
      type Int_Array is array (My_Mod range <>) of Integer;
      subtype My_Arr is Int_Array (1 .. <>);
      X : My_Arr := (1, 2, 3, 4, 5);
      Y : My_Arr := X (2 .. 4);
      W : Int_Array := (6 .. 5 => 0);
      Z : My_Arr := My_Arr (W);
   begin
      pragma Assert (X'First = 1);
      pragma Assert (X (1) = 1);
      pragma Assert (Y'First = 1);
      pragma Assert (Y (1) = 2);
      pragma Assert (Z'First = 1);
   end Test_1;

   procedure Test_2 with Global => null is
      type My_Mod is mod 15;
      type Int_Array is array (My_Mod range <>) of Integer;
      subtype My_Arr is Int_Array (0 .. <>);
      W : Int_Array := (6 .. 5 => 0);
      Z : My_Arr := My_Arr (W); --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_2;

   procedure Test_3 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      subtype My_Arr is Int_Array (1 .. <>);
      function Id (A : My_Arr) return My_Arr is (A);
      X : My_Arr := (1, 2, 3, 4, 5);
      Y : My_Arr := X (2 .. 4);
      W : Int_Array := (6 .. 5 => 0);
      Z : My_Arr := My_Arr (W);
   begin
      pragma Assert (X'First = 1);
      pragma Assert (X (1) = 1);
      pragma Assert (Y'First = 1);
      pragma Assert (Y (1) = 2);
      pragma Assert (Z'First = 1);
      pragma Assert (Id (0 & X)'First = 1);
      pragma Assert (Id (0 & X)'Last = 6);
      pragma Assert (Id (0 & X) (1) = 0);
      pragma Assert (Id (0 & X) (2) = 1);
   end Test_3;

   procedure Test_4 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      subtype My_Arr is Int_Array (10 .. <>);
      function Id (A : My_Arr) return My_Arr is (A);

      function F (A : My_Arr) return Integer with Pre => True is
         Y : Int_Array := A;
      begin
         pragma Assert (Y'First = 10);
         return 1;
      end F;

      C : constant Integer := F ((1, 2, 3));
      X : My_Arr := (1, 2, 3, 4, 5);
      Y : My_Arr := X (11 .. 13);
      W : Int_Array := (6 .. 5 => 0);
      Z : My_Arr := My_Arr (W);
      V : My_Arr := 0 & X;
   begin
      pragma Assert (Id ((1, 2, 3, 4, 5))'First = 10);
      pragma Assert (Id ((1, 2, 3, 4, 5)) (10) = 1);
      pragma Assert (X'First = 10);
      pragma Assert (X (10) = 1);
      pragma Assert (Y'First = 10);
      pragma Assert (Y (10) = 2);
      pragma Assert (Z'First = 10);
      pragma Assert (V'First = 10);
      pragma Assert (V'Last = 15);
      pragma Assert (V (10) = 0);
      pragma Assert (V (11) = 1);
      pragma Assert (Id (0 & X)'First = 10);
      pragma Assert (Id (0 & X)'Last = 15);
      pragma Assert (Id (0 & X) (10) = 0);
      pragma Assert (Id (0 & X) (11) = 1);
   end Test_4;

   procedure Test_5 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      subtype My_Arr is Int_Array (Positive'Last .. <>);
      X : Int_Array := (1, 2, 3);
      Z : My_Arr := X; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_5;

   procedure Test_6 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      function Id (X : Integer) return Integer is (X);
      subtype My_Arr is Int_Array (Id (0) .. <>); --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_6;

   procedure Test_7 (C : Positive) with Global => null, Pre => C <= 1000 is
      type Int_Array is array (Positive range <>) of Integer;
      subtype My_Arr is Int_Array (C .. <>);
      function Id (A : My_Arr) return My_Arr is (A);

      function F (A : My_Arr) return Integer with Pre => True is
         Y : Int_Array := A;
      begin
         pragma Assert (Y'First = C);
         return 1;
      end F;

      D : constant Integer := F ((1, 2, 3));
      X : My_Arr := (1, 2, 3, 4, 5);
      Y : My_Arr := X (C + 1 .. C + 3);
      W : Int_Array := (6 .. 5 => 0);
      Z : My_Arr := My_Arr (W);
      V : My_Arr := 0 & X;
   begin
      pragma Assert (Id ((1, 2, 3, 4, 5))'First = C);
      pragma Assert (Id ((1, 2, 3, 4, 5)) (C) = 1);
      pragma Assert (X'First = C);
      pragma Assert (X (C) = 1);
      pragma Assert (Y'First = C);
      pragma Assert (Y (C) = 2);
      pragma Assert (Z'First = C);
      pragma Assert (V'First = C);
      pragma Assert (V'Last = C + 5);
      pragma Assert (V (C) = 0);
      pragma Assert (V (C + 1) = 1);
      pragma Assert (Id (0 & X)'First = C);
      pragma Assert (Id (0 & X)'Last = C + 5);
      pragma Assert (Id (0 & X) (C) = 0);
      pragma Assert (Id (0 & X) (C + 1) = 1);
   end Test_7;

   procedure Test_8 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      subtype My_Arr is Int_Array (1 .. <>);
      function Id (A : Int_Array) return Int_Array is (A);
      function Id2 (A : My_Arr) return My_Arr is (A);

      X : Int_Array (11 .. 15) := (1, 2, 3, 4, 5);
      Y : My_Arr := My_Arr'(X); --  There will be an index check here once the frontend uses the subtype mark as the Etype of the qualification
   begin
      pragma Assert (Id (My_Arr'(X))'First = 11);
      pragma Assert (Id2 (My_Arr'(X))'First = 1);
   end Test_8;

   procedure Test_10 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      function Id (X : Integer) return Integer is (X);
      subtype My_Arr is Int_Array (1 .. <>);
      subtype My_Arr_Bad is My_Arr (Id (7) .. 8); --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_10;

   procedure Test_11 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      function Id (X : Integer) return Integer is (X);
      subtype My_Arr is Int_Array (1 .. <>);
      subtype My_Arr_2 is My_Arr (Id (1) .. 8);
   begin
      null;
   end Test_11;

   procedure Test_12 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      function Id (X : Integer) return Integer is (X);
      subtype My_Arr is Int_Array (1 .. <>);
      subtype Constr is Int_Array (1 .. Id (2));
      A : My_Arr := (1, 2, 3, 4);
      B : Constr := A; -- @LENGTH_CHECK:FAIL
   begin
      null;
   end Test_12;

   procedure Test_13 with Global => null is
      function Id (X : Integer) return Integer is (X);
      type Index is new Positive range 1 .. 2;
      type Int_Array is array (Index range <>) of Integer;
      subtype My_Arr is Int_Array (1 .. <>);
      type Constr is array (Positive range 1 .. Id (4)) of Integer;
      A : Constr := (1, 2, 3, 4);
      B : My_Arr := My_Arr (A); -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_13;

begin
   Test_1;
   Test_3;
   Test_4;
   Test_7 (15);
   Test_8;
   Test_11;
   Test_13;
end Test_First_Bound;
