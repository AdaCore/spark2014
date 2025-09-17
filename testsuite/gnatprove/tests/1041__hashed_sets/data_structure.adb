package body Data_Structure with SPARK_Mode is

   function Find_Bucket (X : Element_Type; Modulus : Hash_Type) return Hash_Type is
     (Hash (X) mod Modulus + 1);

   procedure Lemma_Equivalent_Elements_Find_Bucket
     (X, Y : Element_Type; Modulus : Hash_Type)
   is
   begin
      Lemma_Equivalent_Elements_Hash (X, Y);
   end Lemma_Equivalent_Elements_Find_Bucket;

end Data_Structure;
