separate (Tasks)
protected body Store_Stub is

   procedure Put (X : Integer) is
   begin
      The_Stored_Data := X;
   end Put;

   entry Wait when True is
   begin
      null;
   end Wait;

end Store_Stub;
