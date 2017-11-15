Package body Proof
with SPARK_Mode
is

   procedure F1 (X : in     T_X1;
                 Y : in     T_Y;
                 Z : in out T_Z)
   is
      T : T_FLOAT32;
   begin
      if not (EQUAL(X, 0.0)) then
         T := Z + X;
         if (Y * T) > 0.0 then
            Z := -Z;
         end if;
      end if;
   end F1;

   procedure F2 (X : in     T_X2;
                 Y : in     T_Y;
                 Z : in out T_Z)
   is
      T : T_FLOAT32;
   begin
      if not (EQUAL(X, 0.0)) then
         T := Z + X;
         if (Y * T) > 0.0 then
            Z := -Z;
         end if;
      end if;
   end F2;

end Proof;


