package body Q with SPARK_Mode is
   package body Bad with SPARK_Mode => Off is
      procedure Dummy is null;
   end;
   procedure Dummy is
   begin
      for J in 1 .. Bad.X.C loop
         null;
      end loop;
   end;
end;
