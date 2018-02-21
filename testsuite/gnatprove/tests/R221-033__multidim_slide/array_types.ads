with Ext; use Ext;
package Array_Types with SPARK_Mode is
   G : constant Positive := X;

   B : M (1 .. 3, G .. G + 2) := New_M;
   pragma Assert (B'First (2) = 1); --@ASSERT:FAIL
end Array_Types;
