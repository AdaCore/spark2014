procedure Pred_On_Out with SPARK_Mode is
   type T1 is record
      X : Integer;
   end record;

   subtype S1 is T1 with
     Predicate => S1.X in Positive;

   procedure P1 (X : out S1) with Global => null
   is
   begin
      X.X := 1;
   end P1;

   procedure Q1 with Global => null
   is
      X : T1;
   begin
      P1 (X);
   end Q1;

   type T2 is record
      X : Integer := 0;
   end record;

   subtype S2 is T2 with
     Predicate => S2.X in Positive;

   procedure P2 (X : out S2) with Global => null
   is
   begin
      X.X := 1;
   end P2;

   procedure Q2 with Global => null
   is
      X : T2;
   begin
      P2 (X);
   end Q2;
begin
   Q1;
   Q2;
end Pred_On_Out;
