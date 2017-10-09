package body Intra_Unit_Elaboration_Order_Examples is

   function F (I : Integer) return Integer is (I + 1);
   --  The early call region for F ends here as the body has been
   --  declared. It can now be called using normal visibility rules.

   procedure P (I : in out Integer) is
   begin
      if I > 10 then
         Q (I);  --  Q is still in the early call region and so this call is
                 --  allowed
      end if;
   end P;
   --  The early call region for P ends here as the body has been
   --  declared. It can now be called using normal visibility rules.

   procedure Q (J : in out Integer) is
   begin
      if J > 20 then
         J := J - 10;
         P (J);  --  P can be called as its body is declared.
      end if;
   end Q;
   --  The early call region for Q ends here as the body has been
   --  declared. It can now be called using normal visibility rules.

   procedure R (Z : in out Integer) is
   begin
      Z := G (Z); --  The expression function G has been declared and
                  --  so can be called
   end R;

   procedure S (A : in out Integer) is
   begin
      A := A + Y; --  Reference to Y is ok because it is in the early call
                  --  region and the Elaborate_Body pragma ensures it is
                  --  initialized before it is used.
   end S;

begin
   Y := 42;
   P (X);   --  Call to P and hence Q during the elaboration of the package.
end Intra_Unit_Elaboration_Order_Examples;
