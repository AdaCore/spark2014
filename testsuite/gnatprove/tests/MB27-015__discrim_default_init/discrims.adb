package body Discrims
  with SPARK_Mode => On
is
   procedure Op (X : in out Integer;
                 Y : in     Natural)
   is
      --  Default discriminant depends no "in" parameter, which is
      --  viewed as a constant, so should be legal.
      --
      --  NOTE - Flow analysis should pick up the dependence
      --  between final value of X and initial value of Y
      type T2N (DN : Integer := Y) is null record; -- legal
      T : T2N;
   begin
      X := X + T.DN;
   end Op;

end Discrims;
