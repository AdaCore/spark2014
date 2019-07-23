with Ada.Text_IO; use Ada.Text_IO;

package body Tictactoe
with SPARK_Mode => On
is

   type Position is record
      X, Y : Pos;
   end record;

   procedure Play (P : Position; V : Slot)
     with Pre => My_Board (P.X)(P.Y) = Empty and V /= Empty,
     Post => Num_Free_Slots = Num_Free_Slots'Old - 1;

   procedure Initialize is
   begin
      My_Board := (others => (others => Empty));
   end Initialize;

   procedure Player_Play is
      P : Position;
   begin
      loop
         declare
            S : String(1..1);
            Last : Natural;
            Found : Boolean := True;
         begin
         Get_Line (S, Last);
         Skip_Line;
            if Last >= 1 then
               declare
                  C : Character := S (S'First);
               begin
                  P := (1, 1);
                  case C is
                     when '1' =>
                        P := (1, 1);
                     when '2' =>
                        P := (2, 1);
                     when '3' =>
                        P := (3, 1);
                     when '4' =>
                        P := (1, 2);
                     when '5' =>
                        P := (2, 2);
                     when '6' =>
                        P := (3, 2);
                     when '7' =>
                        P := (1, 3);
                     when '8' =>
                        P := (2, 3);
                     when '9' =>
                        P := (3, 3);
                     when others =>
                        Found := False;
                  end case;

                  if Found and then My_Board (P.X)(P.Y) = Empty then
                     exit;
                  end if;
               end;
            end if;
         end;
      end loop;

      Play(P, Player);
   end Player_Play;

   type Line is array (1 .. 3) of Position;

   type Solutions is array (Integer range <>) of Line;

   All_Solutions : Solutions(1 .. 8) :=
     (((1, 1), (1, 2), (1, 3)),
      ((2, 1), (2, 2), (2, 3)),
      ((3, 1), (3, 2), (3, 3)),
      ((1, 1), (2, 1), (3, 1)),
      ((1, 2), (2, 2), (3, 2)),
      ((1, 3), (2, 3), (3, 3)),
      ((1, 1), (2, 2), (3, 3)),
      ((1, 3), (2, 2), (3, 1)));

   type Solution_Result is array (1 .. 3) of Slot;

   function Result (L : Line) return Solution_Result is
     (My_Board (L(1).X)(L(1).Y), My_Board (L(2).X)(L(2).Y), My_Board (L(3).X)(L(3).Y));

   procedure Play (P : Position; V : Slot) is
   begin
      My_Board (P.X)(P.Y) := V;
   end Play;

   procedure Computer_Play is
      Score : Integer;
      Target_Scores : array (1 .. 2) of Integer := (2, 20);
      P : Position := (1,1);
      Found : Boolean := False;
   begin
      Search_Loop : for Target_Score in Target_Scores'Range loop

         for S of All_Solutions loop
            Score := 0;

            for I in S'Range loop
               P := S (I);
               if My_Board (P.X)(P.Y) = Computer then
                  Score := Score + 1;
               elsif My_Board (P.X)(P.Y) = Player then
                  Score := Score + 10;
               end if;
            end loop;

            if Score = Target_Scores(Target_Score) then
               for PP of S loop
                  if My_Board (PP.X)(PP.Y) = Empty then
                     Found := True;
                     P := PP;
                     exit Search_Loop;
                  end if;
               end loop;
            end if;
         end loop;
      end loop Search_Loop;

      if Found then
         Play (P, Computer);
         return;
      end if;

      pragma Assert (Num_Free_Slots > 0);

      for I in My_Board'Range loop
         for J in My_Board(I)'Range loop
            if My_Board (I)(J) = Empty then
               Play((I, J), Computer);
               return;
            end if;
         end loop;
      end loop;
   end Computer_Play;

   procedure Display is
   begin
      for J in reverse Pos loop
         for I in Pos loop
            case My_Board (I)(J) is
               when Empty =>
                  Put (".");
               when Player =>
                  Put ("X");
               when Computer =>
                  Put ("O");
            end case;
         end loop;
         New_Line;
      end loop;
   end Display;

   function Won return Slot is
      Score : Integer;
      P : Position;
   begin
      for S of All_Solutions loop
         Score := 0;

         for I in S'Range loop
            P := S (I);

            if My_Board (P.X)(P.Y) = Computer then
               Score := Score + 1;
            elsif My_Board (P.X)(P.Y) = Player then
               Score := Score + 10;
            end if;
         end loop;

         if Score = 3 then
            return Computer;
         elsif Score = 30 then
            return Player;
         end if;
      end loop;

      return Empty;
   end Won;

end Tictactoe;
