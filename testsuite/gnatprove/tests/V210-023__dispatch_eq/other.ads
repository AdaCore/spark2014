package Other is
   type Root is tagged record
      F : Integer;
      D : Natural;
   end record;
   function "=" (X, Y : Root) return Boolean is (X.F = Y.F);

   type Child is new Root with record
      G : Integer;
   end record;

   function Rand (X : Natural) return Natural with
     Import,
     Post => Rand'Result in 1 .. 2;
end Other;
