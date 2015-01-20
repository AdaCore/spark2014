--  This is a flow test, but no flow messages are produced. This is
--  intentional - the final assignment used to crash flow analysis. Proof
--  will pick up that its not OK to do it.

procedure Main
is
   type Discriminant_Type is (A, B);

   type Variant_Type (Discr : Discriminant_Type := A) is
      record
         Common : Integer;

         case Discr is
            when A =>
               null;
            when B =>
               B_Only : Integer;
         end case;
      end record;

   U0 : Variant_Type;
   U1 : Variant_Type (Discr => A) := (Discr => A, Common => 0);
   U2 : Variant_Type (Discr => B) := (Discr => B, Common => 0, B_Only => 0);
begin
   U0 := U2;  --@DISCRIMINANT_CHECK:PASS
   U1 := U0;  --@DISCRIMINANT_CHECK:FAIL
end Main;
