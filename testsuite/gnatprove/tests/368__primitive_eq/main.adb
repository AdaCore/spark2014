procedure Main with SPARK_Mode is
   procedure Test_Subtype is
      type My_Rec is record
         F : Integer;
      end record;
      subtype S is My_Rec with Predicate => S.F /= 0;

      function "=" (X, Y : S) return Boolean is (X.F = Y.F); --@PREDICATE_CHECK:FAIL

      procedure P (X, Y, Z : My_Rec; B : out Boolean) with Pre => True;

      procedure P (X, Y, Z : My_Rec; B : out Boolean) is
      begin
         B := X in Y | Z;
      end P;

      B : Boolean;
   begin
      P ((F => 1), (F => 2), (F => 0), B);
   end test_subtype;

   procedure Test_Pre is
      type My_Rec is record
         F : Integer;
      end record;

      function "=" (X, Y : My_Rec) return Boolean is
        (X.F = Y.F)
        with Pre => X.F > Y.F;--@PRECONDITION:FAIL

      procedure P (X, Y, Z : My_Rec; B : out Boolean) with Pre => True;

      procedure P (X, Y, Z : My_Rec; B : out Boolean) is
      begin
         B := X in Y | Z;
      end P;

      B : Boolean;
   begin
      P ((F => 1), (F => 2), (F => 0), B);
   end Test_Pre;

begin
   Test_Subtype;
end Main;
