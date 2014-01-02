-- MB27-015 - legality of variables in expressions.
--
-- This test case shows examples of both legal and illegal
-- use of variables inside renamings of function calls.
--
-- See SPARK LRM 4.4(2) fifth bullet.
package Q
is
   type T is range 1 .. 10;

   type Arr is array (T) of Boolean;

   Null_Arr : constant Arr := Arr'(others => False);

   Arr_Obj : Arr := Null_Arr;

   V : T := 1;

   function Get_V return T
     with Global => V;

   function Get_P (I : in T) return T;

   function Get_Arr return Arr
     with Global => Arr_Obj;

   function Get_Arr_P1 (X : in Arr) return Arr;

   function Get_Arr_P2 (X : in Arr; I : in T) return Boolean;

end Q;
