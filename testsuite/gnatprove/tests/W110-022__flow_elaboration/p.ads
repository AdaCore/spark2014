package P with Abstract_State => State is
   pragma Elaborate_Body;
private
   X : Integer := 0 with Part_Of => State;
   package Q1 with
     Initializes => (Y => X)
   is
     Y : Integer := X with Part_Of => State;
   end;
   package Q2 with
     Initializes => (Y => State)
   is
     Y : Integer := X with Part_Of => State;
   end;
end;
