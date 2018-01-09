package body P with Refined_State => (Solid_State => X, Task_State => Q.T) is

   X : Boolean := True;

   package Q is
      task T;
   end Q;

   package body Q is
      task body T is
      begin
         loop
            X := not X;
         end loop;
      end T;
   end Q;

   procedure Flip is
   begin
      X := not X;
   end Flip;

end P;
