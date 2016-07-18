with Ada.Containers;

package Aida.Containers with SPARK_Mode is

   subtype Count_Type is Ada.Containers.Count_Type;

   use type Count_Type;

   subtype Hash_Type is Ada.Containers.Hash_Type;

end Aida.Containers;
