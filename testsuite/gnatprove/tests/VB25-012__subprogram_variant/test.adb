procedure Test with SPARK_Mode is

   procedure P1 (X : Integer) with
     Import,
     Global => null,
     Always_Terminates,
     Subprogram_Variant => (Decreases => X);

   procedure P2 (X : Integer) with
     Global => null,
     Always_Terminates,
     Subprogram_Variant => (Decreases => X);

   procedure P2 (X : Integer) is null with
     SPARK_Mode => Off;

   procedure P3 (X : Integer) with
     Global => null,
     Always_Terminates,
     Subprogram_Variant => (Decreases => X);

   procedure P3 (X : Integer) is null;

begin
   null;
end Test;
