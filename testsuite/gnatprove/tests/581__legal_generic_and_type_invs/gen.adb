package body Gen with SPARK_Mode is

   procedure PP (X : in out T) is
   begin
      X := 0;
   end PP;

   package body Nested is
      procedure PPP (X : in out T) is
      begin
         X := 0;
      end PPP;
   end Nested;

   procedure Priv_PP is new PP; --  private instance, invariant check not needed
   package Priv_Nested is new Nested; --  private instance, invariant check not needed

end Gen;
