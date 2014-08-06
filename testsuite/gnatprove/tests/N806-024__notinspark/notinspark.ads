package Notinspark is

   function Get return Integer;

   procedure Set with
     Global => (In_Out => Get);

end Notinspark;
