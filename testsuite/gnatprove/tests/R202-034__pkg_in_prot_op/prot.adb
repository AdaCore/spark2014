package body Prot is
   protected body PT is
      procedure Dummy is
         package P is
            Y : Integer := X;
         end;
      begin
         null;
      end;
   end;
end;
