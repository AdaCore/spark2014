package body Partial_Init is

   procedure Create (V : out T) is
   begin
      pragma Assert (V.X = 0);
   end Create;

   function Create return T is
      V : T;
   begin
      V.Y := (others => 0);
      pragma Assert (V.X = 0);
      return V;
   end Create;

end Partial_Init;
