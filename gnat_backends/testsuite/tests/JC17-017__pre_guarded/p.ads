package P is

   procedure Not_Guarded (X, Y : Integer) with
     Pre => X / Y > 0;

   procedure Guarded_And_Then (X, Y : Integer) with
     Pre => Y /= 0 and then X / Y > 0;

   procedure Guarded_If_Then (X, Y : Integer) with
     Pre => (if Y /= 0 then X / Y > 0);

   procedure No_Need_For_Guard (X, Y : Positive) with
     Pre => X / Y > 0;

end P;
