with Ada.Unchecked_Deallocation;

package Test_Support is

   type Integer_Array is array (Integer range <>) of Integer;

   type Host_Array_Access is access Integer_Array;

   procedure Free is new Ada.Unchecked_Deallocation
     (Integer_Array, Host_Array_Access);

   Host_Array : Host_Array_Access := new Integer_Array'(1 .. 10 => 0);

   Test_Array_Value : Integer_Array := (10, 20, 30, 40, 50, 60, 70, 80, 90, 100);
   Test_Array_Reset : Integer_Array (1 .. 10) := (others => 0);

end Test_Support;
