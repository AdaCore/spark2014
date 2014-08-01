package C330002_0 with SPARK_Mode is

   type Array_Type is array (Positive range <>) of Integer;

   A : constant Array_Type := (83, 36);

   procedure Assign_Array (A : out Array_Type);

   procedure Assign_Array_Post (A : out Array_Type) with
     Post => A = (85, 36);

end C330002_0;
