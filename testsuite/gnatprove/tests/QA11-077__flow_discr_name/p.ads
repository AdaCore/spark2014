package P is
   procedure Write;
   procedure Read_Write;

   procedure Main;

   generic procedure Dummy with Global => null;
end;
