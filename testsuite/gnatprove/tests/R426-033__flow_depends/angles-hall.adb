package body Angles.Hall with
  Refined_State => (State => X) is

   X : Integer := 0;

   procedure Update (Position : out Integer) is
   begin
      null;
   end Update;

   procedure Update is
      Position : Integer;
   begin
      Update (Position);
   end Update;

end Angles.Hall;
