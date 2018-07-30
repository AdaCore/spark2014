package body P is
   A : Integer;

   procedure Proc (X : in out Integer;
                   Y : in out Integer)
     with Depends => (Y => (A , X),
                      X => Y)
   is
   begin
      Y := A;
      X := Y;
      pragma Assert (X = 0);
   end Proc;
end P;
