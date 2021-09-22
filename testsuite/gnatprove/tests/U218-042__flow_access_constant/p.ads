package P with Initializes => null is
   type T is access Integer;
   C : constant T;
private
   C : constant T := new Integer'(0);
end;
