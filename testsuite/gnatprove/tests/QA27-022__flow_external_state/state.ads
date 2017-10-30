package State
with Abstract_State => (State with External => Async_Writers)
is

   procedure Update
   with
      Global => (In_Out => State);

   function Get return Natural;
--   with
--      Global => (Input => State),
--      Volatile_Function;
   --  If all aspects are removed, the use of State.Get in Main is
   --  accepted.

end State;
