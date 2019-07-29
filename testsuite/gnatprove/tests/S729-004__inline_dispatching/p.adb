package body P with SPARK_Mode is

   type D is new T with null record;
   procedure Proc (Self : D; X : Boolean) is
   begin
      pragma Assert (X);  -- @ASSERT:FAIL
   end Proc;

   procedure Test is
      X : D;
      Y : T'Class := X;
   begin
      Proc (X, True);
      Proc (Y, False);
   end Test;

end P;
