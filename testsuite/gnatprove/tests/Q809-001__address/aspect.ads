with Addr;

package Aspect is

   Z : Integer with Address => Addr.F;
   --  the above should be rejected because of the use of a non-SPARK
   --  expression

end Aspect;
