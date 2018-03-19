with Bad;

package P with SPARK_Mode is

   type T is array (1 .. Bad.High) of Integer;
   --  Marking should check the Bad.High constraint

end;
