procedure Conv is

   function Has_Neg_Sign (X : Float) return Boolean is
   begin
      return Float'Copy_Sign (1.0, X) < 0.0;
   end Has_Neg_Sign;

   function Zero return Float is (0.0);

   Z1 : Float := Zero;
   Z2 : Float := -Zero;

   Z1_Sign : constant Boolean := Has_Neg_Sign (Z1);
   Z2_Sign : constant Boolean := Has_Neg_Sign (Z2);
begin
   pragma Assert (Z1_Sign = Z2_Sign); --@ASSERT:FAIL
end Conv;
