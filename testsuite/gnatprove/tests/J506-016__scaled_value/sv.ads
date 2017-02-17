package SV
  with SPARK_Mode
is

   type Base_Type is mod 2 ** 64;
   for Base_Type'Size use 64;

   subtype Capacity_Type is Base_Type range 1 .. 2 ** 32 - 1;
   subtype Request_Type is Base_Type range 0 .. 2 ** 32 - 1;
   subtype Sum_Type is Base_Type range 0 .. Base_Type'Last / 1000;

   function Scale
     (Capacity           : Capacity_Type;
      Requested_Capacity : Sum_Type;
      Value              : Request_Type) return Request_Type with
     Pre => Requested_Capacity > Capacity and Value <= Capacity,
     Post => Scale'Result <= Capacity;

end SV;
