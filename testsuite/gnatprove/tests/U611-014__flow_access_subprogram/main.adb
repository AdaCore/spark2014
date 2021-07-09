procedure Main is
   type Callback is access procedure;

   procedure Fire with
      Global => null
   is
   begin
      null;
   end Fire;

   procedure Test (Cond : Boolean; Call1, Call2 : Callback) with
      Pre    => Call1 /= null and Call2 /= null,
      Global => null
   is
   begin
      if Cond then
         Call1.all;
      else
         Call2.all;
      end if;
   end Test;

   X : Callback := Fire'Access;

begin
   Test (True, X, X);
end Main;
