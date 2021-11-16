package UU
with SPARK_Mode => On
is
   type R (F : Boolean := True) is record
      case F is
         when False =>
            FI : Integer;
         when True =>
            FF : Float;
      end case;
   end record
     with Unchecked_Union;

   package OK is
      type Root is tagged record
         F : Integer;
         G : R;
      end record;
      function "=" (X, Y : Root) return Boolean is (X.F = Y.F);

      function Id (X : Integer) return Integer is (X);

      R1 : constant Root := (F => Id (1), G => (True, 0.0));
      R2 : constant Root := (F => Id (0), G => (False, 0));

      RC1 : constant Root'Class := R1;
      RC2 : constant Root'Class := R2;

      function F (X, Y : Root'Class) return Boolean is
        (X in Y | Root'Class);

      B : Boolean := RC1 /= RC2;
   end OK;

   package Bad is
      type Root is tagged record
         F : Integer;
         G : R;
      end record;

      function Id (X : Integer) return Integer is (X);

      R1 : constant Root := (F => Id (1), G => (True, 0.0));
      R2 : constant Root := (F => Id (0), G => (False, 0));

      RC1 : constant Root'Class := R1;
      RC2 : constant Root'Class := R2;

      function F (X, Y : Root'Class) return Boolean is
        (X in Y | Root'Class); --@UU_RESTRICTION:FAIL

      B : Boolean := RC1 /= RC2;  --@UU_RESTRICTION:FAIL
   end Bad;
end UU;
