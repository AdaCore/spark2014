package body Assume_Call is
   function f1 (X : Integer) return Integer is
   begin
     return X + 1; -- overflow check might fail
   end f1;

   procedure Wrong_Pre (X : Integer) with Pre => X < 0;

   procedure Wrong_Pre (X : Integer) is
   begin
      null;
   end Wrong_Pre;

   procedure Caller is
      Z : Integer := f1 (Integer'Last);
   begin
      Wrong_Pre (Z);
   end Caller;

end Assume_Call;
