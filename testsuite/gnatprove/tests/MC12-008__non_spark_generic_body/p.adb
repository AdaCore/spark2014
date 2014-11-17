with G;
pragma Elaborate_All(G);
with G2;
package body P
  with SPARK_Mode => On
is
   package G1 is new G (T);

   --  Call the local instantiation
   procedure Do_It1 (X : in out T)
   is
   begin
      G2.Op (X);
   end Do_It1;

   --  Call a library-level instantiation
   procedure Do_It2 (X : in out T)
   is
   begin
      G2.Op (X);
   end Do_It2;

end P;
