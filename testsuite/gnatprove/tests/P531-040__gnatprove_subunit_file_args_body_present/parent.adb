package body Parent
   with SPARK_Mode => On
is

procedure P (X : in out T) is
begin
   X := X + 1;
   end P;

end Parent;
