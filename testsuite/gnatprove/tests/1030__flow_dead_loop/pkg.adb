function Pkg return Boolean is
begin
   if True then
      return True;
   else
      declare
         package P with Abstract_State => State, Initializes => State is
            procedure Flip with Global => (In_Out => State);
         end;

         package body P with Refined_State => (State => X) is
            X : Boolean := True;
            procedure Flip with Refined_Global => (In_Out => X) is
            begin
               X := not X;
            end;
         end;
      begin
         P.Flip;
      end;
      return False;
   end if;
end;
