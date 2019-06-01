package Show_Bug with
  SPARK_Mode => On
is

   type A is range 0 .. 0;
   type B is array (A) of Boolean;

   protected Control is

   end Control;

private

   V : B := B'(others => False) with
     Part_Of => Control;

end Show_Bug;
