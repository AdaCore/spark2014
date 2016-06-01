package Simple is

   type T is private;

   procedure Create (X : out T);

   procedure Update (X : in out T);

   function Get (X : T) return Integer;

private

   type T is new Integer with
     Default_Value => 42,
     Type_Invariant => T /= 0;

end Simple;
