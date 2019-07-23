package Info
  with
   SPARK_Mode,
   Abstract_State => (Valid, (State with External => Async_Writers))
is
   pragma Elaborate_Body;

   function Is_Valid return Boolean;

private

   State_Valid : Boolean := False
   with
      Part_Of => Valid;

   function Is_Valid return Boolean is (State_Valid);

end Info;
