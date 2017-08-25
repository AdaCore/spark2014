package body P is
   protected body PT is
      procedure Fetch (X : Integer; Y : out Integer) is
      begin
         Y := Z + X;
      end;

      procedure Proxy (X : Integer; Y : out Integer) is
      begin
         Fetch (X, Y);
      end;
   end;
end;
