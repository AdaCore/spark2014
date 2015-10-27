package PO_T4 is
   --  TU: 5. A type which does not yield synchronized objects shall not have a
   --  component type which yields synchronized objects. [Roughly speaking, no
   --  mixing of synchronized and unsynchronized component types.] In enforcing
   --  this rule, privacy of types is ignored (that is, any partial views of
   --  types are ignored and the corresponding full view is unconditionally
   --  used instead). [TBD: add an aspect to allow this property to be
   --  expressed explicitly when a partial view of a type is declared.]

   protected type Protected_Int is
      procedure Set (X : Integer);
      function Get return Integer;
   private
      Safe_Int : Integer := 10;
   end Protected_Int;

   type Mix is record
      X  : Integer;
      PO : Protected_Int;
   end record with Volatile;
end PO_T4;
