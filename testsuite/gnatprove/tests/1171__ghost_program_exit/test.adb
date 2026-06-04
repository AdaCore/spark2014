procedure Test with SPARK_Mode is

   procedure Non_Ghost_P (X : Boolean) with
     Import,
     Always_Terminates,
     Global => null,
     Program_Exit => not X,
     Post => X;

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
      procedure P3 (X : Boolean) with Ghost is
      begin
        Non_Ghost_P (X); -- @UNEXPECTED_PROGRAM_EXIT:PASS
      end P3;
   begin
      P1 (True); -- @UNEXPECTED_PROGRAM_EXIT:PASS
      P2 (True); -- @UNEXPECTED_PROGRAM_EXIT:PASS
      P3 (True);
   end OK1;

   procedure OK2 with Ghost, Program_Exit => True is
   begin
      P1 (False); -- @UNEXPECTED_PROGRAM_EXIT:NONE
   end OK2;

   procedure OK3 with Ghost, Program_Exit => True is
   begin
      P2 (False); -- @UNEXPECTED_PROGRAM_EXIT:NONE
   end OK3;

   procedure OK4 with Ghost, Program_Exit => True is
      procedure P3 (X : Boolean) with Ghost is
      begin
        Non_Ghost_P (X); -- @UNEXPECTED_PROGRAM_EXIT:NONE
      end P3;
   begin
      P3 (False);
   end OK4;

   procedure Bad1 with Program_Exit => True is
   begin
      P1 (False); -- @UNEXPECTED_PROGRAM_EXIT:FAIL
   end Bad1;

   procedure Bad2 with Program_Exit => True is
   begin
      P2 (False); -- @UNEXPECTED_PROGRAM_EXIT:FAIL
   end Bad2;

   procedure Bad3 with Program_Exit => True is
      procedure P3 (X : Boolean) with Ghost is
      begin
        Non_Ghost_P (X); -- @UNEXPECTED_PROGRAM_EXIT:FAIL
      end P3;
   begin
      P3 (False);
   end Bad3;
begin
   null;
end;
