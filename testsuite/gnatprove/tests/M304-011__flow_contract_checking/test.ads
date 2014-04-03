package Test is

   X, Y, Z: Integer;

   function Check_Contract_1 return Integer;
   --  No global, no depends

   procedure Check_Contract_2 (Par1: Integer; Par2: in out Integer)
   --  No global, correct depends
      with Depends => (Par2 =>+ Par1);

   procedure Check_Contract_3 (X, Y: in out Integer; Z: out Integer)
   --  No global, incorrect depends
      with Depends => (X => Y,
                       Y => X,
                       Z => X);

   procedure Check_Contract_4 (Par1: Integer; Equals: out Boolean)
   --  Correct global, no depends
      with Global => X;

   procedure Check_Contract_5
   --  Correct global, correct depends
      with Global  => (Input  => X,
                       Output => Y,
                       In_Out => Z),
           Depends => (Y =>  (Z, X),
                       Z =>+ X);

   procedure Check_Contract_6 (Par1: Integer; Par2: out Integer)
   --  Correct Global, incorrect depends
      with Global  => (In_Out => X),
           Depends => (Par2 =>  (Par1, X),
                       X    =>+ null);

   function Check_Contract_7 return Integer
   --  Incorrect global, no depends
      with Global => (X, Y);

   procedure Check_Contract_8
   --  Incorrect global, incorrect depends
      with Global  => (In_Out => X,
                       Input  => Y),
           Depends => (X =>+ Y);

end Test;
