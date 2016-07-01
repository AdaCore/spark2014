pragma Profile (Ravenscar);

with GNAT_Bug;

procedure Main
  with SPARK_Mode
is
begin
   GNAT_Bug.PO.Test;
end Main;
