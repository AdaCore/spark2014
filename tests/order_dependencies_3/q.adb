with P; use P;

package body Q is

   procedure Assign_X_To_Y is
   begin
      if X > 0 then
         Y := X - 1;
         Assign_Y_To_X;
      end if;
   end;

end;
