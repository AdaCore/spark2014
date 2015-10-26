package Sort_Types with SPARK_Mode is
   subtype Index is Integer range 1 .. 100;
   subtype Nb_Occ is Integer range 0 .. 100;
   type Nat_Array is array (Index range <>) of Natural;
end Sort_Types;
