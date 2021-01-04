with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;

package P_Colibri with SPARK_Mode is
   subtype Index is Integer range 1 .. 10;

   subtype Small_Float is Float range 0.0 .. 2.0**16;

   type My_Array is array (Index) of Small_Float;

   function fn (n : Index; v : My_Array) return Float is
     (if v(n) >= 0.5 then 1.0 / v(n) else 0.0);

   package Float_Conv is new Float_Conversions (Float);
   use Float_Conv;

   function real_fn (n : Index; v : My_Array) return Valid_Big_Real is
     (if v(n) >= 0.5 then 1.0 / To_Big_Real (v(n)) else 0.0);

   procedure Prove_Bound_fn (n : Index; v : My_Array) with
     Ghost,
     Global => null,
     Post => (declare --@POSTCONDITION:FAIL
                Difference : constant Big_Real := To_Big_Real (fn (n, v)) - real_fn (n, v);
              begin Difference = 0.0);

   procedure Prove_Bound_fn (n : Index; v : My_Array) is null;
end P_Colibri;
