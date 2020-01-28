package P
  with Abstract_State => (State with External => Async_Writers)
is
   X, Y : Integer with Volatile, Async_Writers;
   function F return Integer; -- with Global => (X, Y);

   procedure Update
   with
      Global => (In_Out => State);

   function Get return Natural;
end;
