with Types; use Types;

package Quantifiers with
  SPARK_Mode
is
   --  from K106-005 (example for teaching)
   procedure Previous_Seen (X : Array_10_Integer_32; Y : Index_10);

   --  from N805-028 (example for teaching)
   procedure Not_For_Some (X : Array_10_Integer_32);

end Quantifiers;
