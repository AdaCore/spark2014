package body Discrims
  with SPARK_Mode => On
is
   procedure Op (X : in out Integer;
                 Y : in     Natural)
   is
      --  Default discriminant depends on "in" parameter, which is
      --  viewed as a constant, so should be legal.

      type T0N (DN : Integer := 0) is null record; -- legal - literal

      type T1N (DN : Integer := C0) is null record; -- legal - constant

      type T2N (DN : Integer := Y) is null record; -- legal - in parameter

      type T3N (DN : Integer := X) is null record; -- illegal - in out parameter is a variable

      type T4N (DN : Integer := V0) is null record; -- illegal - variable

      T : T2N;
   begin
      X := X + T.DN;
   end Op;

end Discrims;
