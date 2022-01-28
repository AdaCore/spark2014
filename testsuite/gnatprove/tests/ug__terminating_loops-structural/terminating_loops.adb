package body Terminating_Loops with
  SPARK_Mode
is

   procedure Set_All_To_Zero (L : List) is
      X : access Cell := L;
   begin
      while X /= null loop
	 pragma Loop_Variant (Structural => X);
	 X.Value := 0;
	 X := X.Next;
      end loop;
   end Set_All_To_Zero;

end Terminating_Loops;
