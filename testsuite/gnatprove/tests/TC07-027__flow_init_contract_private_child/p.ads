package P with Abstract_State => State is
private
   Y : Integer with Part_Of => State;
   procedure Init_Y;
end;
