pragma SPARK_Mode;
procedure Update_Lists_Restore (Source, Target : in out List; Key : Character) is
   Rev_Src : List := null;
   Rover : List := Source;
begin
   while Rover /= null loop
      declare
         Next_Rover : constant List := Rover.Next;
      begin
         if Rover.Key = Key then
            -- prepend Rover at head of Target list
            Rover.Next := Target;
            Target := Rover;
            -- update Rover for next iteration
            Rover := Next_Rover;
         else
            -- keep Rover in reversed Source list
            Rover.Next := Rev_Src;
            Rev_Src := Rover;
            -- update Rover for next iteration
            Rover := Next_Rover;
         end if;
      end;
   end loop;

   -- reverse source list into Source
   Rover  := Rev_Src;
   Source := null;
   while Rover /= null loop
      declare
         Next_Rover : constant List := Rover.Next;
      begin
         -- keep Rover in Source list
         Rover.Next := Source;
         Source := Rover;
         -- update Rover for next iteration
         Rover := Next_Rover;
      end;
   end loop;
end Update_Lists_Restore;
