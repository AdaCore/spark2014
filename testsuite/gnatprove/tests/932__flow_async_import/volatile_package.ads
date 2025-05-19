package Volatile_Package with SPARK_Mode => On
is

   type Index_Type is range 192 .. 210; -- Some small, arbitrary range

   Volatile_Variable             : Index_Type with Volatile;
   Volatile_Initialized_Variable : Index_Type := Index_Type'First with Volatile;
   Volatile_Imported_Variable    : Index_Type with Volatile, Import;

end Volatile_Package;
