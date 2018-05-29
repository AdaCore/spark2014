package body P is

   function Target return Integer with Pre => True;

   function Generic_Proxy return Integer is
   begin
      return Target;
   end;

   D : Integer := 0;

   function Target return Integer is
   begin
      return 1/D;
   end;

end;
