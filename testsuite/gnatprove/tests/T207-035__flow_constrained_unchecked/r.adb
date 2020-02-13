procedure R (First, Last : Integer; Data : Integer; Result : out Integer) with
   Depends => (Result => Data, null => (First, Last))
is
   subtype T is Integer range First .. Last;

   procedure Op_Foo (A : in out T) is
   begin
      A := A;
   end Op_Foo;

begin
   Result := Data;
   Op_Foo (Result);
   --  When frontend inlines this procedure call, it will add an unchecked
   --  conversion to T. However, objects referenced in the bounds of T shall
   --  not be pulled as data dependencies of the Result.
end R;
