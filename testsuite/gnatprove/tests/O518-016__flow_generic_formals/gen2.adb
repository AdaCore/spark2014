package body Gen2 is
   procedure Set (V : Integer) is
   begin
      G := V;
   end Set;
   function Get return Integer is (G);
end Gen2;
