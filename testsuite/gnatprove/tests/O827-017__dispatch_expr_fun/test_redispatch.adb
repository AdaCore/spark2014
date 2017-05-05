with Tagged_Types; use Tagged_Types;
procedure Test_Redispatch with SPARK_Mode is
   X : Child := (I => 1, J => 2);
begin
   pragma Assert (G (Root (X)) = 2);
end Test_Redispatch;
