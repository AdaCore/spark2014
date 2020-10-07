package body My_Package with SPARK_Mode is
   procedure My_Proc is
   begin
      My_Int := 4;
   end My_Proc;

   G : Natural;

   procedure Set_G is
   begin
      G := 0;
   end Set_G;

   function Get_G return Natural is (G);

end My_Package;
