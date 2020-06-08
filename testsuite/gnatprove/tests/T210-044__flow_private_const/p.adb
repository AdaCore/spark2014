procedure P with SPARK_Mode => On, Global => null is
   package Pkg is
      C : constant Integer;
   private
      pragma SPARK_Mode (Off);
      C : constant Integer := 0;
   end;
begin
   null;
end;
