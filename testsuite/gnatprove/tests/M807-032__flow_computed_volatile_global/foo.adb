package body Foo
is

   X : Integer with Volatile, Async_Writers, Effective_Reads;

   procedure P_G (N : out Integer)
   with Pre => True
   is
   begin
      N := X;
   end P_G;

   procedure P_C (N : out Integer)
   with Global => (In_Out => X),
        Depends => ((N, X) => X)
   is
   begin
      N := X;
   end P_C;

   procedure P_Wrong (N : out Integer)
   with Depends => (N => X)
   is
   begin
      N := X;
   end P_Wrong;

   procedure Verify_P_G (N : out Integer)
   with Depends => ((N, X) => X)
   is
   begin
      P_G (N);
   end Verify_P_G;

   procedure Verify_P_C (N : out Integer)
   with Depends => ((N, X) => X)
   is
   begin
      P_C (N);
   end Verify_P_C;

   procedure Verify_P_Wrong (N : out Integer)
   with Depends => (N => X)
   is
   begin
      P_Wrong (N);
   end Verify_P_Wrong;

end Foo;
