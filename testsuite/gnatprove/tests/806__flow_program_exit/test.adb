procedure Test with SPARK_Mode is
   G : aliased Integer;

   procedure P1 with
     Import,
     Always_Terminates,
     Global => null,
     Program_Exit => True;

   package P is
      procedure Dummy;
   end;
   package body P is
      procedure Dummy is null;
   begin
      P1;
   end;

   procedure Bad_Call_P1 with
     Global => (In_Out => G),
     Program_Exit => G > 0
   is
   begin
      P1; --  check: G might not be initialized
      G := 11;
   end Bad_Call_P1;

   procedure Ok_Call_P1 with
     Global => (Output => G),
     Program_Exit => G > 0
   is
   begin
      G := 11;
      P1; --  ok, G is initialized before the call to P1
   end Ok_Call_P1;

   procedure P2 with
     Import,
     Always_Terminates,
     Global => (Output => G),
     Program_Exit => G > 0;

   procedure Call_P2 with
     Global => (In_Out => G),
     Program_Exit => G > 0
   is
   begin
      P2; --  ok, G is initialized by P2 (it is in its postcondition)
   end Call_P2;

   procedure P3 with
     Import,
     Always_Terminates,
     Global => (Output => G),
     Program_Exit => True;

   procedure Bad_Call_P3 with
     Global => (In_Out => G),
     SPARK_Mode => Off, --  This is rejected in marking
     Program_Exit => G > 0
   is
   begin
      G := 11;
      P3; --  Here G could be uninitialized by P3
   end Bad_Call_P3;

   procedure Test_Effects with -- There should be no warnings, Test_Effects has some effects
     Global => (In_Out => G),
     Program_Exit => G > 0
   is
   begin
      P1;
   end Test_Effects;
begin
   null;
end;
