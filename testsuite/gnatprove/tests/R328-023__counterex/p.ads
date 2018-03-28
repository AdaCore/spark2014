
package P with SPARK_Mode is

   subtype Index is Integer range 0 .. 38;
   type Arr is array (Index range <>) of Integer;

   function Last_Length (A : Arr; B: Arr) return Integer is
     (A'Last - B'First - 2 * B'Length);

end P;
