package body Pack is
   pragma SPARK_Mode;
   procedure P0 is
      procedure P3 is
      begin
         if Y.all = 0 then
            return;
         end if;
      end;
      procedure P0_Ok is
      begin
         null;
      end;
   begin
      P3;
   end;

   procedure P1 is
      procedure P4 is
      begin
         loop
            exit;
         end loop;
      end;
      procedure P1_Ok is
      begin
         null;
      end;
   begin
      if X then
         return;
      end if;
   end;

   procedure P2 is
   begin
      declare
         procedure P5 is
            type R is record
               X, Y, Z : Integer;
            end record;
            RR : R;
         begin
            RR := (0,1,2);
         end;
         Z : Boolean := X;
         procedure P2_Ok is
         begin
            null;
         end;
      begin
         if Z then
            return;
         end if;
      end;
   end;

end;
