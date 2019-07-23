--  The idea of this test was to verify late marking of incomplete types. I
--  would have liked to put the package in Auto mode, but currently access
--  types declared in parts with auto mode are not supported.

package Incomplete_Type_Auto is
   type W is private;

   W1 : constant W;
   function OK (X : W) return Boolean;
private
   type C;
   type C_Acc is access C;
   type D;
   type D_Acc is access D;
   type C is record
      X : C_Acc;
      Y : D_Acc;
   end record;

   type W is record
      F : Integer;
      H : C_Acc;
   end record;

   W1 : constant W := (F => 1, others => <>);
   function OK (X : W) return Boolean is (X.F = 1);
end Incomplete_Type_Auto;
