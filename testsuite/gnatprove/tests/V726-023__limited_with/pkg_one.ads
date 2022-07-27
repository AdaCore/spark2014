with Pkg_Two;
package Pkg_One with
   SPARK_Mode => On
is
   type Access_T is access all Integer;
   type Record_T is record
      Field : Pkg_Two.Access_T;
   end record;
end Pkg_One;
