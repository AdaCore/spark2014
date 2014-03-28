package body No_Inlining
  with SPARK_Mode
is

   procedure Test_Recursion (Res : out Boolean) is
      function Recurse (X : Boolean) return Boolean;
      function Recurse (X : Boolean) return Boolean is
      begin
         if X then
            return True;
         else
            return Recurse (not X);
         end if;
      end Recurse;
   begin
      Res := Recurse (False);
   end Test_Recursion;

end No_Inlining;
