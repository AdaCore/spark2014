procedure Test with SPARK_Mode is
   G : Natural;

   --  Check that unexpected calls are detected

   procedure P1 with
     Import,
     Always_Terminates,
     Global => null,
     Program_Exit;

   procedure Call_P1 is
   begin
      P1; -- @UNEXPECTED_PROGRAM_EXIT:FAIL
   end Call_P1;

   function F1 return Boolean with
     Import,
     Side_Effects,
     Always_Terminates,
     Global => null,
     Program_Exit;

   procedure P2 with
     Import,
     Always_Terminates,
     Global => (In_Out => (G)),
     Program_Exit => G'Old /= 0 and then G /= 0;

   --  Checks for unexpected program exit

   procedure Call_F1_Ghost with
     Program_Exit;  --  Unreachable branch

   procedure Call_F1_Ghost is
      B : Boolean with Ghost;
   begin
      B := F1; -- @UNEXPECTED_PROGRAM_EXIT:FAIL
   end Call_F1_Ghost;

   procedure Call_P2_No_Exit_OK is
   begin
      P2; -- @UNEXPECTED_PROGRAM_EXIT:FAIL
   end Call_P2_No_Exit_OK;

   procedure Call_P2_No_Exit_Bad is
   begin
      G := 0;
      P2; -- @UNEXPECTED_PROGRAM_EXIT:PASS
   end Call_P2_No_Exit_Bad;

   --  Checks for program exit postcondition

   procedure Call_P1_Post with
     Program_Exit => G = 1; -- @PROGRAM_EXIT_POST:PASS

   procedure Call_P1_Post is
   begin
      G := 1;
      P1; -- @UNEXPECTED_PROGRAM_EXIT:NONE
   end Call_P1_Post;

   procedure Call_P1_Wrong_Post with
     Program_Exit => G = 1; -- @PROGRAM_EXIT_POST:FAIL

   procedure Call_P1_Wrong_Post is
   begin
      P1; -- @UNEXPECTED_PROGRAM_EXIT:NONE
      G := 1;
   end Call_P1_Wrong_Post;

   procedure Call_P2_Post with
     Program_Exit => G > 0; -- @PROGRAM_EXIT_POST:PASS

   procedure Call_P2_Post is
   begin
      P2; -- @UNEXPECTED_PROGRAM_EXIT:NONE
   end Call_P2_Post;

   procedure Call_P2_Wrong_Post with
     Program_Exit => G > 1; -- @PROGRAM_EXIT_POST:FAIL

   procedure Call_P2_Wrong_Post is
   begin
      P2; -- @UNEXPECTED_PROGRAM_EXIT:NONE
   end Call_P2_Wrong_Post;

   --  References to 'Old in Program_Exit

   procedure Call_P1_Post_Old with
     Program_Exit => G = G'Old; -- @PROGRAM_EXIT_POST:PASS

   procedure Call_P1_Post_Old is
   begin
      P1; -- @UNEXPECTED_PROGRAM_EXIT:NONE
   end Call_P1_Post_Old;

   --  Interaction with exit cases

   procedure Call_P2_Exit_Cases_Bad (B : Boolean) with
     Exit_Cases =>
       (B => Normal_Return), --@EXIT_CASE:FAIL
     Program_Exit;

   procedure Call_P2_Exit_Cases_Bad (B : Boolean) is
   begin
      P2;
   end Call_P2_Exit_Cases_Bad;

   procedure Call_P2_Exit_Cases_OK (B : Boolean) with
     Exit_Cases =>
       (B => Normal_Return), --@EXIT_CASE:PASS
     Program_Exit => True;

   procedure Call_P2_Exit_Cases_OK (B : Boolean) is
   begin
      if not B then
         P2;
      end if;
   end Call_P2_Exit_Cases_OK;

   --  Interaction with type invariants

   package Nested is
      type T is private;
   private
      type T is new Integer with
        Default_Value => 0,
        Type_Invariant => T >= 0;
   end Nested;

   package body Nested is
      GT : T;

      --  Check that invariant checks are introduced for outputs on program exit

      procedure Call_P1_OK_Inv with   -- @INVARIANT_CHECK:PASS
        Program_Exit => GT > 0;  -- @PROGRAM_EXIT_POST:PASS
      procedure Call_P1_OK_Inv is
      begin
         GT := 1;
         P1;
      end Call_P1_OK_Inv;

      procedure Call_P1_No_Inv with
        Program_Exit;
      procedure Call_P1_No_Inv is
      begin
         GT := -1;
         P1;
         GT := 0;
      end Call_P1_No_Inv;

      procedure Call_P1_Bad_Inv with  -- @INVARIANT_CHECK:FAIL
        Program_Exit => GT > 0;
      procedure Call_P1_Bad_Inv is
      begin
         GT := -1;
         P1;
         GT := 0;
      end Call_P1_Bad_Inv;

      --  Check that invariant is assumed for outputs on program exit

      procedure P3 with
        Import,
        Always_Terminates,
        Global => (In_Out => (GT)),
        Program_Exit => GT /= 0;

      procedure Call_P3 with    -- @INVARIANT_CHECK:PASS
        Program_Exit => GT > 0; -- @PROGRAM_EXIT_POST:PASS
      procedure Call_P3 is
      begin
         P3;
      end Call_P3;
   end Nested;
begin
   null;
end;
