with SPARK.Lemmas.Mod64_Arithmetic; use SPARK.Lemmas.Mod64_Arithmetic;
with Interfaces; use Interfaces;

package body SV
  with SPARK_Mode
is

   function Scale
     (Capacity           : Capacity_Type;
      Requested_Capacity : Sum_Type;
      Value              : Request_Type) return Request_Type
   is
      Res : Request_Type := (Value * Capacity) / Requested_Capacity;
   begin
      Lemma_Mult_Scale (Val         => Unsigned_64 (Value),
                        Scale_Num   => Unsigned_64 (Capacity),
                        Scale_Denom => Unsigned_64 (Requested_Capacity),
                        Res         => Unsigned_64 (Res));
      return Res;
   end Scale;

end SV;
