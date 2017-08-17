with Addr;

package Attribute is

   Z : Integer;
   for Z'Address use Addr.F;
   --  the above should be rejected because of the use of a non-SPARK
   --  expression

end Attribute;
