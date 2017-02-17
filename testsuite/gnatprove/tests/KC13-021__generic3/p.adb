with Q;

package body P is

   procedure Proc is
   begin
      Y := X;
      Q.Zero;
      if X < 10 then
	 X := X + 1;
      end if;
   end;

end;

