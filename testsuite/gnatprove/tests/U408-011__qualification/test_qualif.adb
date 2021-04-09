procedure Test_Qualif with SPARK_Mode is
   procedure Test1 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      subtype My_Arr is Int_Array with Predicate => My_Arr'First = 1;
      function Id (X : Integer) return Integer is (X);

      X : Int_Array (Id (11) .. 15) := (1, 2, 3, 4, 5);
      Y : Int_Array := My_Arr'(X); --@PREDICATE_CHECK:FAIL
   begin
      null;
   end Test1;

   procedure Test2 with Global => null is
      function Id (X : Integer) return Integer is (X);

      type Rec (D : Integer) is record
         F : Integer;
      end record;
      subtype S is Rec with Predicate => S.F /= 0;

      Z : Rec (1) := (D => 1, F => Id (0));
      W : Rec := S'(Z); --@PREDICATE_CHECK:FAIL
   begin
      null;
   end Test2;

   procedure Test3 with Global => null is
      subtype My_Not_Zero is Integer with Predicate => My_Not_Zero /= 0;
      function Id (X : Integer) return Integer is (X);

      X : Integer := Id (0);
      Y : Integer := My_Not_Zero'(X); --@PREDICATE_CHECK:FAIL
   begin
      null;
   end Test3;
begin
   null;
end Test_Qualif;
