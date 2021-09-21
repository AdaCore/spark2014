package body Q with Refined_State => (S => C) is
   type T is access Boolean;
   C : constant T := null;
   procedure Dummy is null;
end;
