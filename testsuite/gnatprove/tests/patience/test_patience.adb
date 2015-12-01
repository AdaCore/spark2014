with Ada.Text_IO; use Ada.Text_IO;
with Patience; use Patience;


procedure Test_Patience with SPARK_Mode is

   procedure PrintCardStack (S : CardStack) is
   begin
      Put_Line("--------");
      Put("CardStack (first=" & Integer'Image(S'First) & ") = ");
      for I in S'Range loop
         Put(" " & Card'Image(S(I)));
      end loop;
      Put_Line("");
      Put_Line("--------");
   end PrintCardStack;

   procedure PrintState (S : State) is
   begin
      Put_Line("--------");
      Put_Line("Number of elts = " & CardIndex'Image(S.NumElts));
      Put("Card values =");
      for I in 0 .. S.NumElts - 1 loop
         Put(" " & Card'Image(S.Values(I)));
      end loop;
      Put_Line("");
      Put_Line("Number of stacks = " & CardIndex'Image(S.NumStacks));
      for I in 0 .. S.NumStacks - 1 loop
         declare
            Size : CardIndex := S.StackSizes(I);
            Idx : CardIndex;
         begin
            Put("Stack " & CardIndex'Image(I) & " has size " & CardIndex'Image(S.StackSizes(I)) & " :");
            for J in 0 .. S.StackSizes(I) - 1 loop
               Idx := S.Stacks(I)(J);
               Put(" " & CardIndex'Image(Idx) & " =>" & Card'Image(S.Values(Idx)));
            end loop;
            Put_Line("");
         end;
      end loop;
      Put_Line("--------");
   end PrintState;



   Input : CardStack := (9, 7, 10, 9, 5, 4, 10);
   S : State;

begin
   Put_Line ("Test of a patience game");
   PrintCardStack(Input);
   S := PlayGame(Input);
   PrintState(S);
end Test_Patience;
