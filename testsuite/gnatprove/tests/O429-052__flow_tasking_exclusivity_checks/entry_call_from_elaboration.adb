package body Entry_Call_From_Elaboration is

   X : Boolean := True;

   task type TT with Global => X;

   task body TT is
      package Dummy is
         Y : Boolean;
      end;

      package body Dummy is
      begin
         Y := True; --X;
      end;
   begin
      loop
         null;
         Dummy.Y := X;
      end loop;
   end;

   T1, T2 : TT;

end;
