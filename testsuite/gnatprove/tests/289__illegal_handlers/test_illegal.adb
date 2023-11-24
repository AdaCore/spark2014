package body Test_Illegal with SPARK_Mode is

   procedure P is null;

   procedure Call_Handler_1 (X : not null T3) is
   begin
      X.all; --  Illegal, cannot call handler
   end Call_Handler_1;

   procedure Call_Handler_2 (X : not null T3) is
      Y : access procedure := X; --  Illegal, Handler annotation shall be preserved
   begin
      Y.all;
   end Call_Handler_2;

   procedure Nested is
      --  Type declaration not at library level

      type T4 is access procedure with
        Annotate => (GNATprove, Handler);
   begin
      null;
   end Nested;

end;
