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
      AD := D'(1 .. 10 => 10);
      AD (1) := 1;
      G (AD);
   end Try_D;

   procedure Try_E is
      AE : E;
   begin
      AE (1) := 1;
      G (AE);
   end Try_E;

   procedure Local (X : One_Twenty) is
      type Smaller_Local is new Smaller (X - 1 .. X + 1);
      Z : Smaller_Local;
   begin
      Z := Smaller_Local'(X - 1 .. X + 1 => 0);
      Z (X) := 1;
   end Local;

   procedure Loop_Test is
      subtype K is Integer range 11 .. 19;

      X : Integer := 18;
   begin
      for I in K range 12 .. X loop
         null;
      end loop;
      X := X + 1;
      for I in K range 20 .. X loop
         null;
      end loop;
      X := X + 1;

      for I in K range 19 .. X loop -- @RANGE_CHECK:FAIL
         null;
      end loop;
   end Loop_Test;
end Subar;
