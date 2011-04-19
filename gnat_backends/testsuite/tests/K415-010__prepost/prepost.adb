package body Prepost is

   function F (Z : Integer) return Boolean is
   begin
      pragma Assert (Z = 0);
      return True;
   end F;

end Prepost;
