package body Broken
is
   function Bla return Boolean
      with Pre => Bla
   is
   begin
      return True;
   end Bla;
end Broken;
