private package AP.Controls
  with Abstract_State => ((Master_Switch with Part_Of  => AP.State,
                                              External => Async_Writers),
                          (Altitude_Switch with Part_Of  => AP.State,
                                                External => Async_Writers),
                          (Heading_Switch with Part_Of  => AP.State,
                                               External => Async_Writers))
is
   type Switch is (On, Off);

   procedure Read_Master_Switch(Position : out Switch)
     with Global  => (Input  => Master_Switch),
          Depends => (Position => Master_Switch);

   procedure Read_Altitude_Switch(Position : out Switch)
     with Global  => (Input  => Altitude_Switch),
          Depends => (Position => Altitude_Switch);

   procedure Read_Heading_Switch(Position : out Switch)
     with Global  => (Input  => Heading_Switch),
          Depends => (Position => Heading_Switch);
end AP.Controls;
