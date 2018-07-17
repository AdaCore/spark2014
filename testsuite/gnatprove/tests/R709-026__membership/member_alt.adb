procedure Member_Alt with SPARK_Mode is
   type My_Rec (D : Boolean) is record
      F : Integer;
   end record;

   function "=" (X, Y : My_Rec) return Boolean is
     (X.D = Y.D);

   procedure Bad is
      X : My_Rec := (D => True, F => 0);
      Y : My_Rec := (D => True, F => 1);
      Z : My_Rec := (D => True, F => 2);
   begin
      pragma Assert (X = Y);
      pragma Assert (X not in Y | Z); --@ASSERT:FAIL
   end Bad;

   procedure Bad2 is
      X : My_Rec := (D => True, F => 0);

      function F (X : Integer) return My_Rec is
        (D => True, F => X)
        with Pre => X /= 1;
   begin
      pragma Assert (X in F (1) | F (2)); --@PRECONDITION:FAIL
   end Bad2;
begin
   Bad;
end Member_Alt;
