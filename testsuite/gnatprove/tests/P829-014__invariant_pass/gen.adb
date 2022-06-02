package body Gen is

   procedure Swap_T1 (X1 : in out T1) is
   begin
      X1 := (Aaa => X1.Bbb, Bbb => X1. Aaa);
   end;

   procedure Swap_View_Conversion (X : in out D) is
   begin
      Swap_T1 (T1 (X)); -- a view conversion -- no type invariant check here
   end;

end Gen;
