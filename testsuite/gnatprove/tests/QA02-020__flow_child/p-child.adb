package body P.Child is
   procedure Flip with Refined_Global => (In_Out => P.Child.X) is
   begin
      X := not Read_Secret;
   end;
end;
