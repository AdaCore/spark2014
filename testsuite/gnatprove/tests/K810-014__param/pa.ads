package Pa is

   type T (<>) is private;

   function F return T;

private

   type T (D : Integer := 2) is
      record
        X : Integer;
      end record;

end Pa;
