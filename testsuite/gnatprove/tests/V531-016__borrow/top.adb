pragma SPARK_Mode;
procedure Top (B : Boolean) is
   type X is access Integer;
   type T is record
      C : X;
   end record;
   type P is access T;

   V : P;
   W : access T := V;
   U : X := W.C;
begin
   declare
      V : P;
      W : access T := V;
      U : X := W.C;
   begin
      null;
   end;
   declare
      V : P;

      procedure Local with Pre => True is
         W : access T := V;
         U : X := W.C;
      begin
         return;
      end Local;
   begin
      loop
         declare
            W : access T := V;
            U : X := W.C;
         begin
            exit;
         end;
      end loop;

      declare
         W : access T := V;
         U : X := W.C;
      begin
         if B then
            goto Label;
         end if;
      end;

      declare
         W : access T := V;
      begin
         declare
            U : X := W.C;
         begin
            if B then
               goto Label;
            end if;
         end;
      end;
  <<Label>>

      begin
         if B then
            return;
         end if;
      end;

      Local;
   end;
end;
