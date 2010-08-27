package body Random_Numbers
is
   Seed     : Integer;
   Seed_Max : constant Integer := 99;

   function Random return Integer
   is
      My_Stack : ADT_Stack.Stack;
   begin
      ADT_Stack.Pop(My_Stack,Seed);

      if ASM_Stack.Pop <= Seed then
         Seed := ASM_Stack.Pop;
      end if;

      return GCD (Seed, Seed_Max);
   end Random;

   function GCD (M, N : Integer) return Integer
   is
   begin
      if N = 0 then
         return M;
      else
           return GCD (N, M rem N);  -- direct recursion
      end if;
   end GCD;

begin
   Seed := 77;
end Random_Numbers;
