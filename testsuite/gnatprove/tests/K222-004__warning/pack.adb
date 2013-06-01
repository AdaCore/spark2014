package body Pack is
   pragma SPARK_Mode (On);

   function F return Boolean is
      pragma SPARK_Mode (On);
      B : Boolean;
   begin
      B := True;
      return B;
   end F;

   procedure P is
      pragma SPARK_Mode (On);
      B : Boolean;
   begin
      B := False;
      if B then
         null;
      end if;
   end P;
end;
