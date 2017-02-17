package Ar is

   type A is array (1..10) of Integer;
   function Get (X : A) return Integer
      with Post =>
         (Get'Result = X(1));

   procedure Set (X : in out A; Y : Integer)
      with Pre => (1 <= Y and then Y <= 10),
           Post => (X (Y) = 5);
end Ar;
