procedure Test_Reraise with SPARK_Mode is

   E1, E2, E3 : exception;

   type Int_Acc is access Integer;

   --  P1 is OK, X and Y are no longer moved at the end

   procedure P1 (I : Integer; X, Y : aliased in out Int_Acc) is
      Tmp : Int_Acc;
   begin
      begin
         if I in 1 .. 2 then
            Tmp := X;
            if I = 1 then
               raise E1;
            end if;
            X := Y;
            Y := Tmp;
         elsif I in 3 .. 4 then
            Tmp := Y;
            Y := X;
            if I = 3 then
               raise E2;
            end if;
            X := Tmp;
         else
            raise E3;
         end if;
      exception
         when E3 =>
            null;
         when others =>
            raise;
      end;
   exception
      when others =>
         X := Tmp;
   end P1;

   --  P2 is wrong, X might be moved

   procedure P2 (I : Integer; X, Y : aliased in out Int_Acc) is
      Tmp : Int_Acc;
   begin
      begin
         if I in 1 .. 2 then
            Tmp := X;
            if I = 1 then
               raise E1; --  X is moved here
            end if;
            X := Y;
            Y := Tmp;
         elsif I in 3 .. 4 then
            Tmp := Y;
            Y := X;
            if I = 3 then
               raise E2;
            end if;
            X := Tmp;
         else
            raise E3;
         end if;
      exception
         when E3 =>
            null;
         when others =>
            raise; --  E1 is reraised
      end;
   exception
      when E1 =>
         null; --  X is still moved
      when others =>
         X := Tmp;
   end P2;

   --  P3 is wrong, X might be moved

   procedure P3 (I : Integer; X, Y : aliased in out Int_Acc) is
      Tmp : Int_Acc;
   begin
      begin
         if I in 1 .. 2 then
            Tmp := X;
            if I = 1 then
               raise E1;
            end if;
            X := Y;
            Y := Tmp;
         elsif I in 3 .. 4 then
            Tmp := Y;
            Y := X;
            if I = 3 then
               raise E2; --  X is moved here
            end if;
            X := Tmp;
         else
            raise E3;
         end if;
      exception
         when E2 =>
            raise; --  E2 is reraised
         when others =>
            X := Tmp;
            raise;
      end;
   exception
      when others =>
         null; --  X is still moved
   end P3;

   --  P4 is OK, E3 cannot be reraised

   procedure P4 (I : Integer; X, Y : aliased in out Int_Acc) is
      Tmp : Int_Acc;
   begin
      begin
         if I in 1 .. 2 then
            Tmp := X;
            if I = 1 then
               raise E1;
            end if;
            X := Y;
            Y := Tmp;
         elsif I in 3 .. 4 then
            Tmp := Y;
            Y := X;
            if I = 3 then
               raise E2;
            end if;
            X := Tmp;
         else
            raise E3;
         end if;
      exception
         when E3 =>
            null;
         when others =>
            raise;  --  E3 cannot be raised here
      end;
   exception
      when E3 =>
         X := Y; --  This branch is dead
      when others =>
         X := Tmp;
   end P4;

   --  P5 is OK, E3 cannot be reraised

   procedure P5 (I : Integer; X, Y : aliased in out Int_Acc) is
      Tmp : Int_Acc;
   begin
      begin
         if I in 1 .. 2 then
            Tmp := X;
            if I = 1 then
               raise E1;
            end if;
            X := Y;
            Y := Tmp;
         elsif I in 3 .. 4 then
            Tmp := Y;
            Y := X;
            if I = 3 then
               raise E2;
            end if;
            X := Tmp;
         else
            raise E3;
         end if;
      exception
         when E1 | E2 =>
            raise;  --  E3 cannot be raised here
         when others =>
            null;
      end;
   exception
      when E3 =>
         X := Y; --  This branch is dead
      when others =>
         X := Tmp;
   end P5;

begin
   null;
end Test_Reraise;
