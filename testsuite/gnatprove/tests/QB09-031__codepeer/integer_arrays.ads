package integer_arrays with SPARK_Mode is
   type element_type is new Integer;
   type array_type is array (Positive range 1 .. 10) of element_type;
   procedure make_unique(arr: array_type);
end integer_arrays;
