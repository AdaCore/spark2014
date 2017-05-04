package body Bar with SPARK_Mode is
   procedure P is
   begin
      for X in B loop
         pragma Assert (X);
      end loop;
   end P;
end Bar;
