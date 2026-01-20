procedure Test with SPARK_Mode is
   package Nested with Ghost is
      procedure P1 (X : Boolean) with
        Import,
        Always_Terminates,
        Global => null,
        Program_Exit => not X,
        Post => X;

      procedure P2 (X : Boolean) with
        Import,
        Always_Terminates,
        Global => null,
        Exit_Cases =>
          (X => Normal_Return,
           others => Program_Exit);
   end Nested;
   use Nested;

   procedure OK1 is
   begin
      P1 (True); -- @UNEXPECTED_PROGRAM_EXIT:PASS
      P2 (True); -- @UNEXPECTED_PROGRAM_EXIT:PASS
   end OK1;

   procedure OK2 with Ghost, Program_Exit => True is
   begin
      P1 (False); -- @UNEXPECTED_PROGRAM_EXIT:NONE
   end OK2;

   procedure OK3 with Ghost, Program_Exit => True is
   begin
      P2 (False); -- @UNEXPECTED_PROGRAM_EXIT:NONE
   end OK3;

   procedure Bad1 with Program_Exit => True is
   begin
      P1 (False); -- @UNEXPECTED_PROGRAM_EXIT:FAIL
   end Bad1;

   procedure Bad2 with Program_Exit => True is
   begin
      P2 (False); -- @UNEXPECTED_PROGRAM_EXIT:FAIL
   end Bad2;
begin
   null;
end;
