procedure Main is
   type Root_T is tagged null record;
   type Widget_T is new Root_T with record
      X, Y : Integer;
   end record;
   type Nice_Widget_T is new Widget_T with record
      Round : Boolean;
   end record;
   X : Nice_Widget_T := (X     => 1,
                         Y     => 2,
                         Round => False);
   Y : Widget_T'Class := Widget_T'Class (X);
   Z : Nice_Widget_T := Nice_Widget_T (Y); --  valgrind reports no problems
begin
   pragma Assert (X.Round = Z.Round); -- holds at runtime
end;
