function Id (Inx : Integer) return Integer with
  SPARK_Mode,
  Depends => (Id'Result => Inx)

is
   generic
      F : Integer;
   function Proxy return Integer;

   function Proxy return Integer is
   begin
      return F;
   end;

   function Indirect is new Proxy (Inx);

begin
   return Indirect;
end;
