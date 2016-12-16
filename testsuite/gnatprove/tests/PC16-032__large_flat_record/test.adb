package body Test is
   procedure F (X : in out Rec) is begin
      X := (others => 0);
      pragma Assert (X.F_218 = 0);
   end F;
end Test;
