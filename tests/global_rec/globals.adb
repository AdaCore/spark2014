package body Globals is

   G : Integer;

   function Get return Integer is begin return G; end;

   function Get_It return Integer is begin return Get; end;

   procedure Set (X : Integer; Y : out Integer) is begin Y := G; G := X; end;

   procedure Set_It (X : Integer; Y : out Integer) is begin Set (X, Y); end;

end;
