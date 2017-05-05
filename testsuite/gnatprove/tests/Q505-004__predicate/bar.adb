package body Bar with SPARK_Mode is
   procedure P is
   begin
      for X in B range False .. True loop
         null;
      end loop;
   end P;
end Bar;
