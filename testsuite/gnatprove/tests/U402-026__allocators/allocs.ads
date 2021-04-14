package Allocs is

   type T is access Integer;

   function Alloc (V : Integer) return T is (new Integer'(V));
   function Alloc return T;

   type A is array (1 .. 3) of T;

   function Alloc_10 (V : Integer) return A;
   function Alloc_10 return A;

private
   function Alloc return T is (new Integer'(42));

end Allocs;
