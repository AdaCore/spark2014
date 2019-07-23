with Incomplete_Type_Auto; use Incomplete_Type_Auto;
package Use_Incomplete_Type_Auto with SPARK_Mode is
   X : W;
   pragma Assert (OK (W1));
end Use_Incomplete_Type_Auto;
