package body Random_Numbers
is
   Seed     : Integer := 77;
   Seed_Max : constant Integer := 99;

   function Random return Integer
   is
      My_Stack : ADT_Stack.Stack;
   begin
      ADT_Stack.Pop(My_Stack,Seed);

      if ASM_Stack.Pop <= Seed then
         Seed := ASM_Stack.Pop;
      end if;

      return GCD_Function (Seed, Seed_Max);
   end Random;

   function GCD_Function(M, N : Integer) return Integer
   is
      Res : Integer;
   begin
      if N = 0 then
        Res := M;
      else
           Res := GCD_Function (N, M rem N);  -- direct recursion
      end if;
      return Res;
   end GCD_Function;

end Random_Numbers;
