package With_Default with SPARK_Mode is

   procedure Bad_Scalar (C : Natural);

   procedure OK_Scalar (C : Natural);

   procedure Bad_Array1 (C : Natural);

   procedure Bad_Array2 (C : Natural);

   procedure OK_Array (C : Natural);

   procedure OK_Record (C : Natural);

   procedure Bad_Record1 (C : Natural);

   procedure Bad_Record2 (C : Natural);

   procedure Bad_Record3 (C : Natural);

   procedure Bad_Nested_Defaults1 (C : Natural);

   procedure Bad_Nested_Defaults2 (C : Natural);

   procedure Ok_Nested_Defaults (C : Natural);

end With_Default;
