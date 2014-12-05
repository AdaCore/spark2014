package P1
  with Abstract_State => State,
       Initializes    => State
is
   function Read_From_State return Integer;
end P1;
