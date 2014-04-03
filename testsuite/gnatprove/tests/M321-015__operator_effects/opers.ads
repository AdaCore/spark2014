package Opers is

   type My_Int is new Integer range 1 .. 10;

   function "+" (X, Y : My_Int) return My_Int is (10);
   function "<" (X, Y : My_Int) return Boolean is (True);
   function "=" (X, Y : My_Int) return Boolean is (False);

   generic
      type T is private;
      with function "+" (X, Y : T) return T is <>;
   function Apply_To_Self (X : T) return T;

   generic
      type T is private;
      with function "<" (X, Y : T) return Boolean is <>;
   function Compare_With_Self (X : T) return Boolean;

   generic
      type T is private;
      with function "=" (X, Y : T) return Boolean is <>;
   function Equal_With_Self (X : T) return Boolean;

   procedure Test (A : in out Integer);

end Opers;
