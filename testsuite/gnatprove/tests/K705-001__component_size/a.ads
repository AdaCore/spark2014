package A
is
   type Data_Type is range 0..1_000_000_000;
   for Data_Type'Size use 8 * 4;

   type Array_Range is range 1..4;

   type Array_Type is Array (Array_Range) of Data_Type;
   for Array_Type'Component_Size use 8 * 4;

   function test return Boolean with
     Post => Test'Result;

end A;
