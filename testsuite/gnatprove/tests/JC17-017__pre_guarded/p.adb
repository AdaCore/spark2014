package body P is

   procedure Not_Guarded (X, Y : Integer) is begin null; end;

   procedure Guarded_And_Then (X, Y : Integer) is begin null; end;

   procedure Guarded_If_Then (X, Y : Integer) is begin null; end;

   procedure No_Need_For_Guard (X, Y : Positive) is begin null; end;

end P;
