with Pkg;
procedure Main
with SPARK_Mode,
     Pre => not Pkg.Configured
is
begin
   Pkg.Configure;
end Main;
