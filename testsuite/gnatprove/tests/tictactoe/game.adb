with Tictactoe; use Tictactoe;
with Ada.Text_IO; use Ada.Text_IO;

procedure Game
  with SPARK_Mode => On
is
   Player_Turn : Boolean := True;
begin
   Initialize;

   while not Is_Full
     and then Won = Empty
   loop
      if Player_Turn then
         Put_Line ("Player");
         Player_Play;
      else
         Put_Line ("Computer");
         Computer_Play;
      end if;

      Display;
      Player_Turn := not Player_Turn;
   end loop;

   case Won is
      when Computer =>
         Put_Line ("Really, losing against tic tac toe???");
      when Player =>
         Put_Line ("Will try using a deep learning algorithm next time...");
      when Empty =>
         Put_Line ("What's the other kind?");
   end case;
end Game;
