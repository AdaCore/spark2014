with Ext;
package Foo with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   subtype Empty is Integer range 1 .. Id (0);
   C : Empty := Ext.X; --@RANGE_CHECK:FAIL

   procedure P;
end Foo;
