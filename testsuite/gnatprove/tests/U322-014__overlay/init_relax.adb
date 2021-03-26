procedure Init_Relax with SPARK_Mode is

   X : Integer with Alignment => 32, Relaxed_Initialization;
   Y : Integer with Address => X'Address, Import, Alignment => 32;

   procedure P (A : in out Integer) with Pre => True;
   procedure P (A : in out Integer) is
   begin
      A := A / 2;
   end P;

begin
   P (Y);
end Init_Relax;
