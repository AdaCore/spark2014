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

private

   type T1 (D : Integer := X) is record
      null;
   end record;

end P;
