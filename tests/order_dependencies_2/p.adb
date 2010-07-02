package body P is

   function F return Boolean;

   procedure Q is
   begin
      X := F;
   end Q;

   function F return Boolean is
   begin
      return True;
   end F;

end P;
