package body Pack is pragma SPARK_Mode (On);

   procedure P0 is
   begin
      null;
   end;

   procedure P1 is
   begin
      if X then
         return;
      end if;
   end;

   procedure P2 is
   begin
      declare
         Z : Boolean := X;
      begin
         if Z then
            return;
         end if;
      end;
   end;

   procedure P3 is
      pragma SPARK_Mode (Off);
      type Acc is access Integer;
      Y : Acc;
   begin
      if Y.all = 0 then
         return;
      end if;
   end;

   procedure P4 is
   begin
      loop
         exit;
      end loop;
   end;

   procedure P5 is
      type R is record
         X, Y, Z : Integer;
      end record;
      RR : R;
   begin
      RR := (0,1,2);
   end;

end;
