with Q; use Q;

package body P is

   procedure Assign_Y_To_X is
   begin
      if Y > 0 then
         X := Y - 1;
         Assign_X_To_Y;
      end if;
   end;

end;
