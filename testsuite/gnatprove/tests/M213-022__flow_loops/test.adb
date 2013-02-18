package body Test is

   procedure Basic_Loop (X : in out Integer)
   is
   begin
      loop
         X := X + 1;
         X := X / 2;
      end loop;
   end Basic_Loop;

   procedure Is_Prime (N : Positive;
                       P : out Boolean)
   is
   begin
      for I in Positive range 2 .. N / 2 loop
         if N mod I = 0 then
            P := False;
            return;
         end if;
      end loop;
      P := True;
   end Is_Prime;

   procedure Loop_Exits (X : in out Integer;
                         Y : in Integer)
   is
   begin
      My_Loop : loop
         X := 0;
         for I in Integer range 0 .. 10 loop
            X := I;
            exit My_Loop when X > Y;
         end loop;
         X := X;
      end loop My_Loop;
      X := 5;
   end Loop_Exits;

   procedure While_Loop (X : in Natural;
                         Y : out Integer)
   is
   begin
      Y := 0;
      while X /= Y loop
         Y := Y + 1;
      end loop;
   end While_Loop;

end Test;
