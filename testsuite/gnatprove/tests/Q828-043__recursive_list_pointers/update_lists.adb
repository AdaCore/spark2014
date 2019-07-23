pragma SPARK_Mode;
procedure Update_Lists (Source, Target : in out List; Key : Character) is
   procedure Assign (Target, Source : in out List) with Pre => True is
   begin
      Target := Source;
      Source := null;
   end Assign;

   Prev  : List := null;
   Rover : List;
begin
   Assign (Rover, Source);
   while Rover /= null loop
      if Rover.Key = Key then
         -- remove Rover from Source list
         if Prev = null then
            -- removing first list element
            Assign (Source, Rover.Next);
         else
            -- removing subsequent list element
            Assign (Prev.Next, Rover.Next);
         end if;

         declare
            Next_Rover : List;
         begin
            Assign (Next_Rover, Rover.Next);

            -- prepend Rover at head of Target list
            Assign (Rover.Next, Target);
            Assign (Target, Rover);

            -- update Rover for next iteration
            Assign (Rover, Next_Rover);
         end;
      else
         Assign (Prev, Rover);
         Assign (Rover, Prev.Next);
      end if;
   end loop;
end Update_Lists;
