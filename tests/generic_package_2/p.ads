generic
   X : Integer;
   Y : in Integer;
   Z : Integer := 1;
   T : in Integer := 2;

   type T1 is private;
   type T2 is private;
   type T3 is private;

   with function F1 (J : Integer) return Integer;
   with procedure P1 (J : in out Integer);

package P is

   type R is record
      A : T1;
      B : T2;
      C : T3;
      D : Integer;
   end record;

   function Pack (A : T1; B : T2; C : T3) return R;

end;
