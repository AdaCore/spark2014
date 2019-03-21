pragma SPARK_Mode;
procedure Update_Lists_Inlined (Source, Target : in out List; Key : Character) is
   Prev  : List := null;
   Rover : List;
begin
   Rover := Source;
   Source := null;
   while Rover /= null loop
      if Rover.Key = Key then
         -- remove Rover from Source list
         if Prev = null then
            -- removing first list element
            Source := Rover.Next;
            Rover.Next := null;
         else
            -- removing subsequent list element
            Prev.Next := Rover.Next;
            Rover.Next := null;
         end if;

         declare
            Next_Rover : List;
         begin
            Next_Rover := Rover.Next;
            Rover.Next := null;

            -- prepend Rover at head of Target list
            Rover.Next := Target;
            Target := null;
            Target := Rover;
            Rover := null;

            -- update Rover for next iteration
            Rover := Next_Rover;
            Next_Rover := null;
         end;
      else
         Prev := Rover;
         Rover := null;
         Rover := Prev.Next;
         Prev.Next := null;
      end if;
   end loop;
end Update_Lists_Inlined;
