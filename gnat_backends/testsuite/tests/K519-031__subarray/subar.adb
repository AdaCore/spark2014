package body Subar is

   procedure F (X : A) is
   begin
      pragma Assert (X (1) = 1);
      null;
   end F;

   procedure Try_B is
      AB : B;
   begin
      F (AB);
   end Try_B;

end Subar;
