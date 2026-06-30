procedure Test_Relaxed with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type R is record
      F, G : Integer;
   end record;

   X : R with Relaxed_Initialization;

   procedure Write_F with
     Modifies => X.F;

   procedure Write_F is
   begin
      X.F := 12;
   end Write_F;

   procedure Call_Write_F with
     Post => X.G'Initialized = X.G'Initialized'Old
     and then (if X.G'Initialized then X.G = X.G'Old);

   procedure Call_Write_F is
   begin
      Write_F;
   end Call_Write_F;

   procedure Write_X_When_B (B : Boolean) with
     Modifies => (X when B);

   procedure Write_X_When_B (B : Boolean) is
   begin
      if B then
         X := (12, 12);
      end if;
   end Write_X_When_B;

   procedure Call_Write_X_When_B (B : Boolean) with
     Post =>
       (if not B then
          X.F'Initialized = X.F'Initialized'Old
        and then X.G'Initialized = X.G'Initialized'Old
        and then (if X.F'Initialized then X.F = X.F'Old)
        and then (if X.G'Initialized then X.G = X.G'Old));

   procedure Call_Write_X_When_B (B : Boolean) is
   begin
      Write_X_When_B (B);
   end Call_Write_X_When_B;

begin
   null;
end;
