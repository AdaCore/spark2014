package body Null_Concat is
   pragma SPARK_Mode (On);

   procedure P_Good is
      A1 : constant My_Arrays := (1 .. -5 => 0);
      A2 : constant My_Arrays := (1 .. 5 => 1, 6 .. 10 => 2);
      A3 : constant My_Arrays := A1 & A2;
      A4 : constant My_Arrays := A1 & 2;
   begin
      pragma Assert (A3'First = 1);
      pragma Assert (A3 (1) = 1);
      pragma Assert (A4'First = Integer'First);
      pragma Assert (A4 (A4'First) = 2);
   end P_Good;

   procedure P_Bad is
      A1 : constant My_Arrays := (1 .. -5 => 0);
      A2 : constant My_Arrays := (1 .. 5 => 1, 6 .. 10 => 2);
      A3 : constant My_Arrays := A1 & A2;
   begin
      pragma Assert (A3'First = 1);
      pragma Assert (A3 (1) = 2);
   end P_Bad;
end;
