package body Subar is

   procedure F (X : A) is
   begin
      pragma Assert (X (1) = 1);
      null;
   end F;

   procedure Try_B is
      AB : B;
   begin
      AB (1) := 1;
      F (AB);
   end Try_B;

   procedure G (X : C) is
   begin
      pragma Assert (X (X'First) = 1);
      null;
   end G;

   procedure Try_D is
      AD : D (1..10);
   begin
      AD (1) := 1;
      G (AD);
   end Try_D;

   procedure Try_E is
      AE : E;
   begin
      AE (1) := 1;
      G (AE);
   end Try_E;

end Subar;
