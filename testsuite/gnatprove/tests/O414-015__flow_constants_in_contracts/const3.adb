procedure Const3 (X : in     Integer;
                  Y : in     Integer;
                  F :    out Integer;
                  L :    out Integer;
                  R :    out Integer)
  with Pre     => X < Y,
       Depends => (F => X,
                   L => Y,
                   R => (X, Y))
is
   C1 : constant Integer := X;
   C2 : constant Integer := Y;

   subtype Range_T is Integer range C1 .. C2;

   type Array_T is array (Range_T) of Integer;

   A  : Array_T := Array_T'(others => 0);

   procedure Nested (F : out Integer;
                     L : out Integer;
                     R : out Integer)
     with Global  => (C1, C2, A),
          Depends => (F => C1,
                      L => C2,
                      R => (C1, C2, A))
   is
   begin
      R := 0;
      for It in A'Range loop
         R := R + It;
      end loop;

      F := Array_T'First;
      L := Array_T'Last;
   end Nested;
begin
   Nested (F, L, R);
end Const3;
