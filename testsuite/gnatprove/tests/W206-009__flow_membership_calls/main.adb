procedure Main is
   type T is new Integer;

   function Is_Zero (X : T) return Boolean is (X = 0);

   function Are_Zeros (X, Y : T) return Boolean is
      subtype Checked_Zero is T with Predicate => Is_Zero (Checked_Zero);
   begin
      --  When collecting function calls from the following return expression
      --  we will traverse the predicate expression twice and we must cope with
      --  repeated processing of the same call to Is_Zero.
      return X in Checked_Zero and Y in Checked_Zero;
   end;
begin
   null;
end;
