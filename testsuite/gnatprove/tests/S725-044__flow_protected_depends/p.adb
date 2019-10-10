package body P is
   protected body PT is
      procedure Put (X : Integer) is
      begin
         Priv := X;
      end;

      function Get return Integer is
      begin
         return Priv;
      end;
   end;

   R : Rec;

   procedure Test (X1, X2 : Integer; Y : out Integer)
     with Global => (In_Out => R), Depends => (R => (R,X1,X2), Y => (R,X1))
   is
   begin
      R.C1.Put (X1);
      R.C2.Put (X2);
      Y := R.C1.Get;
   end;
end;
