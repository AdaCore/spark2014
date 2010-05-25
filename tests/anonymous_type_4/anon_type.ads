------------------------------------------------------------------------------
--  Test the anonymous type in for statement see .adb
--
package Anon_Type is

   -- type Matrix_Index is range 0 .. 9;
   type Matrix is array (Integer range 0 .. 9,Integer range 0 .. 9)
   	of Integer range 0 .. 999;

   procedure Multiply (X,Y : in Matrix; Z : out Matrix);

end Anon_Type;

