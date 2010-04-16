package body Globals is

   function Direct_Read return Integer is
   begin
      return G;
   end Direct_Read;

   procedure Direct_Write is
   begin
      G := 0;
   end Direct_Write;

   procedure Direct_Read_Write is
   begin
      G := G + 1;
   end Direct_Read_Write;

   function Indirect_Read return Integer is
      X : Integer;
      
      procedure Local (Proxy : in Integer)
	--# global out X;
      is
      begin
	 X := Proxy;
      end Local;
   begin
      Local (G);
      return X;
   end Indirect_Read;

   procedure Indirect_Write is
      procedure Local (Proxy : out Integer) is
      begin
	 Proxy := 0;
      end Local;
   begin
      Local (G);
   end Indirect_Write;

   procedure Indirect_Read_Write is
      procedure Local (Proxy : in out Integer) is
      begin
	 Proxy := Proxy + 1;
      end Local;
   begin
      Local (G);
   end Indirect_Read_Write;

end Globals;
