procedure Discr is
   type Rect (I, J : Integer) is record
      null;
   end record;
   type Square (K : Integer) is new Rect(K,K);
   procedure P (X : in Rect) is
      Y : Square := Square(X);  --  BAD
   begin
      null;
   end;
   X : Rect(1,2);
begin
   P (X);
end Discr;
