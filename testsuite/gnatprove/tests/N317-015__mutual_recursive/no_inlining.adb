package body No_Inlining
  with SPARK_Mode
is

   procedure Test_Recursion (Res : out Boolean) is
      function Recurse1 (X : Boolean) return Boolean;
      function Recurse2 (X : Boolean) return Boolean;

      function Recurse1 (X : Boolean) return Boolean is
         Tmp : Boolean;
      begin
         if X then
            Tmp := True;
         else
            Tmp := Recurse2 (not X);
         end if;
         return Tmp;
      end Recurse1;

      function Recurse2 (X : Boolean) return Boolean is
         Tmp : Boolean;
      begin
         if X then
            Tmp := True;
         else
            Tmp := Recurse1 (not X);
         end if;
         return Tmp;
      end Recurse2;
   begin
      Res := Recurse1 (False);
   end Test_Recursion;

end No_Inlining;
