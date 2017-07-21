pragma SPARK_Mode(ON);

package body cast_array is
   function cast (input_array : in Int_array1) return Int_array2 is
      result : Int_array2;
   begin
      for i in input_array'Range loop
         result(i) := input_array(i);
         pragma Loop_Invariant (for all K in Int_array2'First .. i =>
                                  result(K) = input_array(K));
      end loop;
      return result;
   end cast;


end cast_array;
