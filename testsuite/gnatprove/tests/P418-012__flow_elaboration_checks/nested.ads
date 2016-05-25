package Nested with
   Abstract_State => State
is

   procedure Dummy;

   package P with
      Initializes => X
   is
      X : Integer := 0;
   end P;

end Nested;
