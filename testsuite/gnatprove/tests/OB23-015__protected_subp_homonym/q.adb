package body Q is

   task body TT is
      X : Boolean;
      Y : Integer;

      procedure Set (Q : Boolean) is
      begin
         X := Q;
      end;

      procedure Set (Q : Integer) is
      begin
         Y := Q;
      end;

   begin
      Set (False);
      Set (5);
   end;

end;
