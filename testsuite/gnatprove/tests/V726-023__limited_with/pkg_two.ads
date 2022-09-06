limited with Pkg_One;
package Pkg_Two with
   SPARK_Mode => On
is
   type Function_Pointer_T is access function
     (Handle : Pkg_One.Access_T)
      return Integer;
   type Record_T is record
      Mount : Function_Pointer_T;
   end record;
   type Access_T is access all Record_T;
   type Function_Return_Limited is access function
     (Handle : Integer)
      return Pkg_One.Access_T;
   type Access_Access_T is access Pkg_One.Access_T;
end Pkg_Two;
