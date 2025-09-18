package P
  with Abstract_State => Full_State
is
   function Read_Private_And_Body_State return Boolean
   with Global => (Input => Full_State);
private
   Private_State : Boolean := True
   with Part_Of => Full_State;
end;
