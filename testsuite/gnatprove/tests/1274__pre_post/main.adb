procedure Main with SPARK_Mode is
   function F return Boolean is (True) with SPARK_Mode => Off;

   procedure P;

   procedure P is
      pragma Postcondition (F);
   begin
      null;
   end P;

   procedure P2;

   procedure P2 is
      pragma Precondition (F);
   begin
      null;
   end P2;

begin
   null;
end;
