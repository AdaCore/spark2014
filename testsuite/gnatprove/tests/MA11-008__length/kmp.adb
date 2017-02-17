package body Kmp
   with SPARK_Mode
is

   function Init_Next (P : A) return A is
      Next : A (P'Range) := (others => 0);
      pragma Unreferenced (P);
   begin
      return Next;
   end Init_Next;

end Kmp;
