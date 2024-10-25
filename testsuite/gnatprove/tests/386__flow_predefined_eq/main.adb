with Types; use Types;
with Gen;

procedure Main with SPARK_Mode, Always_Terminates is
begin
   if Chi."=" (Chi.G, Chi.G) then null; end if;
end Main;
