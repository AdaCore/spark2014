--  MB27-015 - test cases for LRM 4.4(2) - contexts requiring
--  a "variable free" expression.
--
--  This case deals with the expression that initializes a default discriminant

package Discrims
  with SPARK_Mode => On
is
   C0 : constant Integer := 0;

   V0 : Integer := 0;

   type T1 (D1 : Integer := 0) is null record;  -- legal

   type T2 (D2 : Integer := C0) is null record; -- legal

   type T3 (D2 : Integer := V0) is null record; -- illegal - init of D2 depends on variable


   --  As above, but private
   type T1p (D1 : Integer := 0) is private;  -- legal

   type T2p (D2 : Integer := C0) is private; -- legal

   type T3p (D2 : Integer := V0) is private; -- illegal - init of D2 depends on variable


   --  Shows how a nested type disciminant can depend on an "in" param
   --  See body.
   procedure Op (X : in out Integer;
                 Y : in     Natural)
     with Depends => (X => (X, Y));

private
   type T1p (D1 : Integer := 0) is null record;

   type T2p (D2 : Integer := C0) is null record;

   type T3p (D2 : Integer := V0) is null record; -- illegal


end Discrims;
