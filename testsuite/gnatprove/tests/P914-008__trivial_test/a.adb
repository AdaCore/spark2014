with SPARK.Unconstrained_Array_Lemmas;

package body A with SPARK_Mode => On is

   type Array_Float_U is array (Index_Type range <>) of Element_Float;

   package SP is new SPARK.Unconstrained_Array_Lemmas
     (Index_Type => Index_Type,
      Element_T  => Element_Float,
      A          => Array_Float_U,
      Less       => "<");

   procedure Test (A : Array_Type) is
   begin
      pragma Assert (for all I in A'Range =>
                       (for all J in A'Range =>
                          (if I < J then A (I) < A (J))));
   end Test;

   procedure Test_Float (A : Array_Float) is
   begin
      SP.Lemma_Transitive_Order (Array_Float_U (A));
      pragma Assert (for all I in A'Range =>
                       (for all J in A'Range =>
                          (if I < J then A (I) < A (J))));
   end Test_Float;

end A;
