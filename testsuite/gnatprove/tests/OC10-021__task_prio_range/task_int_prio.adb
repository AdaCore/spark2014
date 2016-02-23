package body Task_Int_Prio is

   task body TT is
      X : Boolean := True;
   begin
      loop
         X := not X;
      end loop;
   end;

end;
