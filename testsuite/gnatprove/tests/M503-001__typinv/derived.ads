package Derived is

   type T is tagged private;
   type D is tagged private;

   procedure Create (X : out T);

   procedure Update (X : in out T);

   function Get (X : T) return Integer;

   procedure Create (X : out D);

   procedure Update (X : in out D);

   function Get (X : D) return Integer;

private

   type T is tagged record
      C : Integer := 42;
   end record
     with Type_Invariant => T.C /= 0;

   type D is new T with null record;

end Derived;
