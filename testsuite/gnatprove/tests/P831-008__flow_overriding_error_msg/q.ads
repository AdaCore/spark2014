with P; use P;
package Q
is
   function Heap return Boolean;

   type S is new T with record
      Y : Integer;
   end record;

   overriding procedure Proc (A : S);

end Q;
