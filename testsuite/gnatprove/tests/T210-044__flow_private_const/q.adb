procedure Q with SPARK_Mode => On, Global => null is
   package Pkg is
      C : constant Integer;
      D : constant Integer := 0;
      --  we want to try making the CFG more uniform for both constants
   private
      pragma SPARK_Mode (Off);
      C : constant Integer := 0;
   end;
begin
   null;
end;
