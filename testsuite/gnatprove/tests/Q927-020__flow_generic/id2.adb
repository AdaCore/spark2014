function Id2 (Inx : Integer) return Integer with
  SPARK_Mode,
  Depends => (Id2'Result => Inx)

is
   generic
      F : Integer;
   package Proxy with Initializes => (X => F) is
      X : constant Integer := F;
   end;

   package Dummy    is new Proxy (123);
   package Indirect is new Proxy (Inx);

begin
   return Indirect.X;
end;
