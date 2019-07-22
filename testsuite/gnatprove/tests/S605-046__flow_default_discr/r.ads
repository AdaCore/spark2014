package R is
   V : Integer := 0;
   type T is private;
private
   pragma SPARK_Mode (Off);
   type T (D : Integer := V) is null record;
   --  Variable input in default expression, but flow should never peek behind
   --  SPARK_Mode => Off.
end;
