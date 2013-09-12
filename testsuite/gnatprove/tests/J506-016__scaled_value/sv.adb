package body SV is  

   function Scale
     (Capacity           : Capacity_Type;
      Requested_Capacity : Sum_Type;
      Value              : Request_Type) return Request_Type
   is
   begin
      return (Value * Capacity) / Requested_Capacity;
   end Scale;

end SV;
