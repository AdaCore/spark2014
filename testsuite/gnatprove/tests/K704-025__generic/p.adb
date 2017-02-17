
with Gen;
procedure P is
   package Q is new Gen(Integer);

   X : Integer;
begin
   X := Q.Echo (3);
   pragma Assert (X = 3);
end P;
