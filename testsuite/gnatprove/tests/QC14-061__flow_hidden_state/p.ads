package P with Abstract_State => State is

   procedure Dummy with Global => null;

   X : Integer := 0;

private
   Y : constant Integer := X with Part_Of => State;
   --  Constant with variable input; flow insists on the Part_Of, and
   --  consequently it must be listed in Refined_State; fair.
end;
