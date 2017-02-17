procedure Discr_Init with
  SPARK_Mode
is
   type A1 is array (Natural range <>) of Boolean;
   type R1 (J : Integer) is record
      case J is
         when Positive =>
            Arr : A1(1 .. J) := (others => True);
         when others =>
            null;
      end case;
   end record;
   subtype R2 is R1(10);

   X : R2;
   Y : R2;
begin
   X.Arr(1) := Y.Arr(10);
end;
