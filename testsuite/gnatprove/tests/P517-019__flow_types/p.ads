package P is
   X : Integer := 0;
   --  variable input

   type T1 (D : Integer := X) is private; -- error
   --  private type; completed in the private part of the package

   type T2 is record
      Str : String (1 .. X); -- error
   end record;
   --  implicit subtype declaration for a record component

   type T3 (D : Integer := X); -- error
   --  incomplete type; completed in the same part where declared

   type T3 (D : Integer := X) is record
      null;
   end record;

   type T4 is array (1 .. X) of Integer;         -- error
   --  implicit subtype declaration for an array index

   type T5 is array (1 .. 2) of String (1 .. X); -- error
   --  implicit subtype declaration for an array component

   type T6 is array (Integer range <>) of String (1 .. X); -- error

   type T7; --error

   type T7 is array (Integer range <>) of Integer range 1 .. X;

   type T8 is private with Predicate => Integer (T8) > X; -- error

   type T9 is private with Predicate => Integer (T9) > X;

   type T10 is private;

private

   type T1 (D : Integer := X) is record
      null;
   end record;

   type T8 is new Integer;

   type T9 is new Integer with Invariant => True;

   type T10 is new Integer with Predicate => Integer (T10) > X;

end P;
