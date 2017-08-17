with Addr;

package Attribute_And_Aspect is

   Z1 : Integer;
   for Z1'Address use Addr.F;

   Z2 : Integer with Address => Addr.F;

   --  the above should be rejected because of the use of a non-SPARK
   --  expression

end Attribute_And_Aspect;
