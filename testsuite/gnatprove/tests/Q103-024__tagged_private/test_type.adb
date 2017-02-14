with Types; use Types;
procedure Test_Type with SPARK_Mode is
   X : Types.P;
begin
   pragma Assert (Valid (X));
end Test_Type;
