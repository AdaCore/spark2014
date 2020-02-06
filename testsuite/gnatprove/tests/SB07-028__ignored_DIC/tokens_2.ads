package Tokens_2 with SPARK_Mode,
  Initial_Condition => Init is

   package Nested with SPARK_Mode is
      type Cont is private;
      function Length (X : Cont) return Integer;
   private
      pragma SPARK_Mode (Off);
      type Cont is null record;
      function Length (X : Cont) return Integer is (0);
   end Nested;

   C : Integer := 12;

   type Token_Set is private with Ghost, --@DEFAULT_INITIAL_CONDITION:FAIL
     Default_Initial_Condition => T_Length (Token_Set) + C = 7; --@OVERFLOW_CHECK:FAIL
   function T_Length (X : Token_Set) return Integer with Ghost;

   function Init return Boolean with Ghost;

private
   type Token_Set is new Nested.Cont;

   function T_Length (X : Token_Set) return Integer is (Length (X));

   X : Token_Set with Ghost;

   function Init return Boolean is
     (Length (X) + C = 7);

end Tokens_2;
