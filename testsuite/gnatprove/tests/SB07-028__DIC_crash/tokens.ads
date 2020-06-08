package Tokens with SPARK_Mode,
  Initial_Condition => Init is

   package Nested with SPARK_Mode is
      type Cont is private with
        Default_Initial_Condition => Length (Cont) = 0;
      function Length (X : Cont) return Integer;
   private
      pragma SPARK_Mode (Off);
      type Cont is null record;
      function Length (X : Cont) return Integer is (0);
   end Nested;

   type Token_Set is private with Ghost;

   function Init return Boolean with Ghost;

private

   type Token_Set is new Nested.Cont;

   X : Token_Set with Ghost;

   function Init return Boolean is
     (Length (X) = 0);

end Tokens;
