pragma SPARK_Mode(ON);


package cast_array is
   subtype Integer_subtype is Integer;
   type Int_array1 is array (0..2) of Integer;
   type Int_array2 is array (0..2) of Integer_subtype;

   function cast (input_array : Int_array1) return Int_array2 with
     Post => (for all K in Int_array2'Range =>
                cast'Result (K) = input_array(K));
end cast_array;
