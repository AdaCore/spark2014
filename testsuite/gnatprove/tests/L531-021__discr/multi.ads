package Multi is

   type Count is new Integer range 0 .. 20;

   type A is array (Count range <>) of Integer;

   type Both (X : Count) is record
      Base : Integer;
      case X is
         when 0 =>
            null;
         when 1 =>
            Elt : Integer;
         when others =>
            Stock : A (1 .. X);
      end case;
   end record;

end Multi;
