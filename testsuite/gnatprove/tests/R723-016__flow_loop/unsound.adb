package body Unsound is
   procedure Initialize (X : out T) is
   begin
      for J in X'Range loop
         declare
            procedure Dummy is
            begin
               return;
            end;
         begin
            X (J) := 0;
         end;
      end loop;
   end;
end;
