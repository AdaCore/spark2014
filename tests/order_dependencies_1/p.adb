package body P is

   procedure Q is
   begin
      X := F;
   end Q;

   function F return Boolean is
   begin
      return True;
   end F;

end P;
