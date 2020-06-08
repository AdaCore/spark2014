package Time
   with Abstract_State => (s with External => Async_Writers),
        Initializes    => s
is
   procedure Dummy;
end Time;
