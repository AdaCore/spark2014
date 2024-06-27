package body Foo with SPARK_Mode is
   protected body T is
      function Get (Y : out Boolean) return Boolean is
      begin
         Y := X;
         return X;
      end Get;

      procedure Proc (Y : out Boolean) is
         Z : Boolean;
      begin
         Z := Get (Y);  --  internal call from protected procedure
         Y := Y and Z;
      end Proc;

      function Simple return Boolean is
         A, B : Boolean;
      begin
         A := Get (B);  --  internal call from protected function
         return A and B;
      end;
   end T;

   PO : T;

   A, B : Boolean;
begin
   A := PO.Get (B);  --  external call from protected function
end Foo;
