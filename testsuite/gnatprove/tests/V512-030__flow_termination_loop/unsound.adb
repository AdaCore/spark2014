package body Unsound with
   SPARK_Mode => On
is

   function Find_False (My_Array : My_Array_Type) return My_Range_Type is
      Result : My_Range_Type := My_Range_Type'First;
   begin
      loop
         for I in My_Range_Type loop
            if My_Array (I) = False then
               Result := I;
               exit;
            end if;
         end loop;
         exit when My_Array (Result) = False;
      end loop;
      return Result;
   end Find_False;

end Unsound;
