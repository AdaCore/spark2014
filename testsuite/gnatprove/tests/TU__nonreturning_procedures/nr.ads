package NR
is
   X : Integer := 0;

   procedure P with Global => null, No_Return, Import, Convention => C;

   procedure Op1
     with Global => (In_Out => X),
          Pre => X > 0,
          Post => X = X'Old + 1;

   procedure Op2
     with Global => (In_Out => X),
          Pre => X > 0,
          Post => X = X'Old + 1;

end NR;
