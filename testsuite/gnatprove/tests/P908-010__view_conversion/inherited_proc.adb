with Types_With_Inv; use Types_With_Inv;
with Ada.Text_IO;
procedure Inherited_Proc with SPARK_Mode is
   X : T2;
   Y : T2;
begin
   Test (X);
end Inherited_Proc;
