package P is

   type A is array (Integer range 1 .. 10, Integer range 2 .. 11) of Integer;

   type R is record
      FA : A;
   end record;

   procedure P (X : in out A) with
      Pre  => (X (1, 2) < 20),
      Post => (X (1,2) <= 20 and then
               X (1,3) = X'Old (1,3) and then
               X (2,2) = X'Old (2,2));

   procedure Q (Z : in out R) with
      Pre => (Z.FA (1,2) < 20);

end P;
