package Q with Abstract_State => State
is
   G : Integer := 3;
   procedure Dummy;
   function F return Integer is (G);
private
   B : constant Integer := F;
end;
