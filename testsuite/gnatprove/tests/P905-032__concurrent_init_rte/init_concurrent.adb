package body Init_Concurrent with SPARK_Mode is

   protected body Wrong_Init is
      function Get_V return Natural is (V);
      procedure Set_V (X : Natural) is
      begin
         V := X;
      end Set_V;
   end;
end Init_Concurrent;
