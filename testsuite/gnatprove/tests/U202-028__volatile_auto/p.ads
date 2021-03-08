package P is
   X : Integer := 0 with Volatile;

   Y : Integer := X + X;
   --  Illegal in SPARK, but not checked by the frontend

   package Q with SPARK_Mode is
      Z : Integer := Y;
      --  Illegal in SPARK, because the initial expression is illegal
   end;
end;
