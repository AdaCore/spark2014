package Pack is
   pragma SPARK_Mode;
   X : Boolean;

   type Acc is access Integer;
   Y : Acc;

   type R is record
      X, Y, Z : Integer;
   end record;
   Z : R;

   procedure P0 with Pre => Z.X = Z.Y;

   procedure P1 with Post => Y.all = 0;

   procedure P2 with Pre => (if X then True else False);

end;
