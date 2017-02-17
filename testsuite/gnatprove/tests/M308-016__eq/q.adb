package body Q is
   function Change (X : T) return T is
      Res : T := X;
   begin
      case Res.B is
         when True =>
            Res.A := 0;
         when False =>
            Res.C := False;
      end case;
      return Res;
   end Change;

   procedure Update (X, Y : in out T) is
   begin
      X := Change (X);
      Y := Change (Y);
   end Update;
end Q;
