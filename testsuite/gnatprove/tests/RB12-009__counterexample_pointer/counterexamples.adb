procedure Counterexamples (C : Integer) with SPARK_Mode is
   type Int_Access is access Integer;
   type Two_Access is record
      First  : Int_Access;
      Second : Int_Access;
   end record;
   type String_Access is access String;

   type String_Array is array (Positive range <>) of String_Access;

   type Nat_Array is array (Positive range <>) of Natural;

   type Nat_Array_Access is access Nat_Array;

   type String_Array_Access is access String_Array;

   procedure Bad_1 (X : Two_Access) with
     Pre => X.Second /= null
   is
   begin
      pragma Assert (X.First.all = 1); --@ASSERT:FAIL
      pragma Assert (X.Second.all = 1); --@ASSERT:FAIL
   end Bad_1;

   procedure Bad_2 with Pre => True is
      Y : Int_Access := new Integer'(10);
   begin
      pragma Assert (Y.all >= C); --@ASSERT:FAIL
   end Bad_2;

   procedure Bad_3 with Pre => True is
      V : String_Access := new String'("hello");
   begin
      pragma Assert (V.all'Length <= C); --@ASSERT:FAIL
   end Bad_3;

   procedure Bad_4 with Pre => True is
      W : String_Access := new String'("world");
      A : String_Array_Access := new String_Array'(1 => W);
   begin
      pragma Assert (A (1) (3) /= 'r'); --@ASSERT:FAIL
   end Bad_4;

   procedure Bad_5 with Pre => True is
      W : String_Access := new String'("world");
      A : String_Array_Access := new String_Array'(1 => W);
   begin
      pragma Assert (A (1).all'Length < C); --@ASSERT:FAIL
   end Bad_5;

   procedure Bad_6 (D : Positive) with Pre => True is
      A : Nat_Array_Access := new Nat_Array'(1 .. D => 1);
   begin
      pragma Assert (C in A.all'Range); --@ASSERT:FAIL
      pragma Assert (A (C) = 15); --@ASSERT:FAIL
   end Bad_6;

   X : Two_Access;
begin
   null;
   Bad_1 (X); --@PRECONDITION:FAIL
end Counterexamples;
