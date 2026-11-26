with Interfaces;

procedure Accepted_Views with SPARK_Mode is
   subtype Byte is Interfaces.Unsigned_8;
   use type Byte;
   type Pair is record
      Low, High : aliased Byte;
   end record;
   subtype Ordered is Pair with
     Dynamic_Predicate => Ordered.Low <= Ordered.High;

   --  A constant view cannot invalidate the enclosing predicate

   P : constant Ordered := (1, 4);
   Constant_View : constant Byte with Import, Address => P.Low'Address;

   --  A mutable component view without an enclosing predicate is supported

   Q : Pair := (1, 4);
   Mutable_View : Byte with Import, Address => Q.Low'Address;
begin
   pragma Assert (Constant_View = 1);
   Mutable_View := 5;
   pragma Assert (Mutable_View = 5);
end Accepted_Views;
