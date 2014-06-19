package body Gen is
   procedure Set (V : Integer) is
   begin
      G := V;
   end Set;
   function Get return Integer is
   begin
      return G;
   end Get;
end Gen;
