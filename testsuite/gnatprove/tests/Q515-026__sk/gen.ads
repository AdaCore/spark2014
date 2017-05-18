generic
   type Elem is private;

package Gen
  with SPARK_Mode => On
is
   type T is private;

   Val : constant T;

   function Get_Val (E : Elem) return T
   is (Val)
     with
     Post => Get_Val'Result = Get_Val'Result;

private
   pragma SPARK_Mode (Off);

   type T is new Integer;
   Val : constant T := 0;

end Gen;
