package P
  with Abstract_State => State
is
   function Add (X, Y : Integer) return Integer;

   procedure Initialize;
end P;
