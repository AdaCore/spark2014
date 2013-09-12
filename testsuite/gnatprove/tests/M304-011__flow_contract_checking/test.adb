package body Test is 
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

   ----------------------
   -- Check_Contract_1 --
   ----------------------

   function Check_Contract_1 return Integer
   is
      Temp: Integer;
   begin
      if X > 0 then
         Temp := X;
      end if;
      Temp := Y;    --  This statement renders everything above it ineffective.
      return Temp;  --  Check_Contract_2'Result depends only on Y.
   end Check_Contract_1;

   ----------------------
   -- Check_Contract_2 --
   ----------------------

   procedure Check_Contract_2 (Par1: Integer; Par2: in out Integer)
   is
      Temp: Integer := 0;
   begin
      while Temp <= Par1 loop
         Par2 := Par2 * Temp;
      end loop;
   end Check_Contract_2;

   ----------------------
   -- Check_Contract_3 --
   ----------------------

   procedure Check_Contract_3 (X, Y: in out Integer; Z: out Integer)
   is
   begin
      Z := X;
      X := Y;
      Y := X;  --  Y depends on itself rather than X (as stated in the contract).
   end Check_Contract_3;

   ----------------------
   -- Check_Contract_4 --
   ----------------------

   procedure Check_Contract_4 (Par1: Integer; Equals: out Boolean)
   is
   begin
      if Par1 = X then
         Equals := True;
      else
         Equals := False;
      end if;
   end Check_Contract_4;

   ----------------------
   -- Check_Contract_5 --
   ----------------------

   procedure Check_Contract_5
   is
   begin
      if X > Z then
         Y := 10;
      else
         Y := 20;
      end if;

      Z := X + Z;
   end Check_Contract_5;

   ----------------------
   -- Check_Contract_6 --
   ----------------------

   procedure Check_Contract_6 (Par1: Integer; Par2: out Integer)
   is
   begin
      if Par1 > 0 then
         X := 4;  --  X depends on both X and Par1 (not only on X as stated in the contract).
         return;
      end if;

      Par2 := X;  --  Formal parameter Par2 might not be set (if Par1 > 0 then we return).
   end Check_Contract_6;

   ----------------------
   -- Check_Contract_7 --
   ----------------------

   function Check_Contract_7 return Integer
   is
   begin
      return X + Y + Z;  --  Z was not mentioned in the Global aspect.
   end Check_Contract_7;

   ----------------------
   -- Check_Contract_8 --
   ----------------------

   procedure Check_Contract_8
   is
   begin
      X := X + Y - Z;  --  Z was not mentioned in either the Global or Depends aspects.
   end Check_Contract_8;
end Test;
