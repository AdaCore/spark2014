package body Bad is

   procedure P is
      procedure Nested with Annotate => (Gnatprove, Skip_Proof);

      procedure Nested is
      begin
         pragma Assert (F);
      end Nested;
   begin
      pragma Assert (F);
   end P;

end Bad;
