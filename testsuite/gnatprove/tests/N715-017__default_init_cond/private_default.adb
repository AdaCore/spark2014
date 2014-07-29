package body Private_Default with SPARK_Mode => Off is
   procedure Set_Glob (X : Natural) is
   begin
      Glob := X;
   end Set_Glob;
end;
