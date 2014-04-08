package body No_Inlining
  with SPARK_Mode
is

   procedure Test_Recursion (Res : out Boolean) is
      function Recurse (X : Boolean) return Boolean;
      function Recurse (X : Boolean) return Boolean is
         Tmp : Boolean;
      begin
         if X then
            Tmp := True;
         else
            Tmp := Recurse (not X);
         end if;
         return Tmp;
      end Recurse;
   begin
      Res := Recurse (False);
   end Test_Recursion;

end No_Inlining;
