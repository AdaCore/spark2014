procedure Test_Program_Exit with SPARK_Mode is
   G, H : Integer := 0;

   procedure Exit_Program with
     Import, No_Return, Global => null, Program_Exit;

   --  Only outputs referenced outside 'Old need to be preserved

   procedure Unmentioned (Can_Modify : Boolean) with
     Global => (In_Out => (G, H)),
     Pre => G = 0,
     Modifies => (H, G when Can_Modify),
     No_Return,
     Program_Exit => H = 1;

   procedure Unmentioned (Can_Modify : Boolean) is
   begin
      G := 1;
      H := 1;
      Exit_Program;
   end Unmentioned;

   procedure Old_Only (Can_Modify : Boolean) with
     Global => (In_Out => (G, H)),
     Pre => G = 0,
     Modifies => (H, G when Can_Modify),
     No_Return,
     Program_Exit => H = G'Old + 1;

   procedure Old_Only (Can_Modify : Boolean) is
   begin
      G := 1;
      H := 1;
      Exit_Program;
   end Old_Only;

   procedure Mentioned (Can_Modify : Boolean) with
     Global => (In_Out => (G, H)),
     Pre => G = 0,
     Modifies => (H, G when Can_Modify), --  @MODIFIES:FAIL
     No_Return,
     Program_Exit => G = 1 and H = 1;

   procedure Mentioned (Can_Modify : Boolean) is
   begin
      G := 1;
      H := 1;
      Exit_Program;
   end Mentioned;

   type Pair is record
      F, G : Integer;
   end record;
   X : Pair := (0, 0);

   procedure Partial with
     Global => (In_Out => X),
     Pre => X.G = 0,
     Modifies => X.F,
     No_Return,
     Program_Exit;

   procedure Partial is
   begin
      X.G := 1;
      Exit_Program;
   end Partial;

   package Nested with Abstract_State => State is
      function Get_F return Integer with Global => State;

      --  Input-only constituents need no preservation predicate

      procedure Input_Constituent (Can_Modify : Boolean) with
        Global => (In_Out => State),
        Pre => Get_F = 0,
        Modifies => (State when Can_Modify),
        No_Return,
        Program_Exit;

      procedure Unmentioned_State (Can_Modify : Boolean) with
        Global => (In_Out => State),
        Modifies => (State when Can_Modify),
        No_Return,
        Program_Exit;

      procedure Mentioned_State (Can_Modify : Boolean) with
        Global => (In_Out => State),
        Pre => Get_F = 0,
        Modifies => (State when Can_Modify), --  @MODIFIES:FAIL
        No_Return,
        Program_Exit => Get_F = 1;
   end Nested;

   package body Nested with Refined_State => (State => (F, G)) is
      F, G : Integer := 0;

      function Get_F return Integer is (F) with Refined_Global => F;

      procedure Input_Constituent (Can_Modify : Boolean) is
      begin
         G := 1;
         Exit_Program;
      end Input_Constituent;

      procedure Unmentioned_State (Can_Modify : Boolean) is
      begin
         F := 1;
         G := 1;
         Exit_Program;
      end Unmentioned_State;

      procedure Mentioned_State (Can_Modify : Boolean) is
      begin
         F := 1;
         G := 1;
         Exit_Program;
      end Mentioned_State;
   end Nested;
begin
   null;
end Test_Program_Exit;
