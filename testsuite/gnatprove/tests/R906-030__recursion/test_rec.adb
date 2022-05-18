procedure Test_Rec with SPARK_Mode is

   subtype Small_Nat is Natural range 0 .. 100;
   subtype Small_Pos is Positive range 1 .. 100;
   type My_Arr is array (Small_Pos range <>) of Small_Nat;

   function Sum (M : My_Arr) return Natural is
     (if M'Length = 0 then 0
      else Sum (M (M'First .. M'Last - 1)) + M (M'Last))
       with Post => Sum'Result <= 100 * M'Length;
   pragma Annotate (GNATprove, Always_Return, Sum);

   procedure Prove_Sum_Eq (A, B : My_Arr) with
     Ghost,
     Pre  => A = B,
     Post => Sum (A) = Sum (B)
   is
   begin
      if A'Length = 0 then
         return;
      end if;
      Prove_Sum_Eq (A (A'First .. A'Last - 1), B (B'First .. B'Last - 1));
   end Prove_Sum_Eq;

   function Id (X : My_Arr) return My_Arr with Pre => True;
   function Id (X : My_Arr) return My_Arr is
   begin
      return X;
   end Id;


   procedure truncate (M : in out My_Arr; S : Natural) with
     Post => Sum (M) <= S
   is
      CS  : Natural := 0;
      O_M : My_Arr := M with Ghost;
   begin
      for I in M'Range loop
         if CS + M (I) > S then
            M (I) := S - CS;
         end if;
         CS := CS + M (I);
         Prove_Sum_Eq (M (M'First .. I - 1), O_M (M'First .. I - 1));
         pragma Loop_Invariant (CS = Sum (M (M'First .. I)));
         pragma Loop_Invariant (S >= CS);
         O_M := M;
      end loop;
   end truncate;


   X : My_Arr := (1, 2, 3);
   M : My_Arr := Id (X);

   package Nested is
      pragma Assert (Sum (M) <= 100 * M'Length);
   end Nested;
begin
   pragma Assert (Sum (X) <= 300);
   pragma Assert (Sum (X) = 6);
   pragma Assert (Sum (M) <= 100 * M'Length);
end;
