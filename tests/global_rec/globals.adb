package body Globals is
   
   G : Integer;
   
   function Get return Integer is begin return G; end;
   
   function Get_It return Integer is begin return Get; end;
   
   procedure Set (X : Integer; Y : out Integer) is begin G := X; Y := G; end;
   
   procedure Set_It (X : Integer; Y : out Integer) is begin Set (X, Y); end;
   
end;
