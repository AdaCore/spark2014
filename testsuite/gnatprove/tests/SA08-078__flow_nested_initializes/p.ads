package P is
   package Q is
      X : Integer;
   end Q;
   procedure Zero (Arg : out Integer) with Global => null;
end P;
