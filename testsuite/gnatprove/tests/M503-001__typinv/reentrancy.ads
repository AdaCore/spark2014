package Reentrancy is

   type T is private;

   procedure Create (X : out T);

   procedure Update (X : in out T);

   function Get (X : T) return Integer;

private

   type T is new Integer with
     Type_Invariant => T /= 0;

end Reentrancy;
