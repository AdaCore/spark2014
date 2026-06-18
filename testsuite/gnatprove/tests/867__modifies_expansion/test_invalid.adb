procedure Test_Invalid with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type RR is record
      F, G : Positive;
   end record;

   type R is record
      V : RR;
      H : Integer;
   end record;

   X : R with Potentially_Invalid;

   procedure Write_F with
     Modifies => X.V.F;

   procedure Write_F is
   begin
      X.V.F := 12;
   end Write_F;

   procedure Call_Write_F with
     Post => X.V.G'Valid = X.V.G'Valid'Old
       and X.H = X.H'Old,
     Contract_Cases =>
       (X.V.G'Valid => X.V.G = X.V.G'Old,
        others => True);

   procedure Call_Write_F is
   begin
      Write_F;
   end Call_Write_F;

   procedure Write_X_When_B (B : Boolean) with
     Modifies => X when B;

   procedure Write_X_When_B (B : Boolean) is
   begin
      if B then
         X := ((12, 12), 12);
      end if;
   end Write_X_When_B;

   procedure Call_Write_X_When_B (B : Boolean) with
     Post =>
       (if not B then
          X.V.F'Valid = X.V.F'Valid'Old
        and then X.V.G'Valid = X.V.G'Valid'Old
        and then X.H = X.H'Old),
       Contract_Cases =>
         (not B and X'Valid_Scalars =>
            X = X'Old,
          not B and X.V.F'Valid and not X.V.G'Valid =>
            X.V.F = X.V.F'Old,
          not B and not X.V.F'Valid and X.V.G'Valid =>
            X.V.G = X.V.G'Old,
          others => True);

   procedure Call_Write_X_When_B (B : Boolean) is
   begin
      Write_X_When_B (B);
   end Call_Write_X_When_B;

   type A is array (1 .. 2) of Positive;

   Y : A with Potentially_Invalid;

   procedure Write_1 with
     Modifies => Y (1);

   procedure Write_1 is
   begin
      Y (1) := 12;
   end Write_1;

   procedure Call_Write_1 with
     Post => Y (2)'Valid = Y (2)'Valid'Old,
     Contract_Cases =>
       (Y (2)'Valid => Y (2) = Y (2)'Old,
        others => True);

   procedure Call_Write_1 is
   begin
      Write_1;
   end Call_Write_1;

   procedure Write_Y_When_B (B : Boolean) with
     Modifies => Y when B;

   procedure Write_Y_When_B (B : Boolean) is
   begin
      if B then
         Y := (12, 12);
      end if;
   end Write_Y_When_B;

   procedure Call_Write_Y_When_B (B : Boolean) with
     Post =>
       (if not B then
          Y (1)'Valid = Y (1)'Valid'Old
        and then Y (2)'Valid = Y (2)'Valid'Old),
       Contract_Cases =>
         (not B and Y'Valid_Scalars =>
            Y = Y'Old,
          not B and Y (1)'Valid and not Y (2)'Valid =>
            Y (1) = Y (1)'Old,
          not B and not Y (1)'Valid and Y (2)'Valid =>
            Y (2) = Y (2)'Old,
          others => True);

   procedure Call_Write_Y_When_B (B : Boolean) is
   begin
      Write_Y_When_B (B);
   end Call_Write_Y_When_B;

begin
   null;
end;
