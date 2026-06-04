pragma Ada_2022;
procedure Main with SPARK_Mode is
   type A is array (Integer range <>) of Integer;
   procedure Increment (Arr : in out A; F, L, I : Integer)
     with Pre =>
       Arr'First <= F
       and then L <= Arr'Last
       and then (if I in Arr'Range then Arr (I) < Arr'Last),
       Post => (if F <= I and I <= L then Arr (I) = Arr (I)'Old + 1); --@INDEX_CHECK:PASS
   procedure Increment (Arr : in out A; F, L, I : Integer) is
   begin
      if I in F .. L then
         Arr (I) := Arr (I) + 1;
      end if;
   end Increment;
   procedure Nested (X, Y : A; F, L, I : Integer)
     with Pre =>
       X'First <= F
       and then L <= X'Last
         and then Y'First <= F
       and then L <= Y'Last,
       Post => (if F <= I and I <= L then
                  (if F <= X (I)'Old and X (I)'Old <= L then --@INDEX_CHECK:PASS
                     Y (X (I))'Old = Y (X (I)))); --@INDEX_CHECK:PASS
   procedure Nested (X, Y : A; F, L, I : Integer) is null;
   procedure Nested_KO (X, Y : A; F, L, I : Integer)
     with Pre =>
       X'First <= F
       and then L <= X'Last
         and then Y'First <= F
       and then L <= Y'Last,
       Post => (if F <= I and I <= L then
                  (if F <= X (I)'Old and L <= X (I)'Old then --@INDEX_CHECK:PASS
                     Y (X (I))'Old = Y (X (I)))); --@INDEX_CHECK:FAIL
   procedure Nested_KO (X, Y : A; F, L, I : Integer) is null;
begin
   null;
end Main;
