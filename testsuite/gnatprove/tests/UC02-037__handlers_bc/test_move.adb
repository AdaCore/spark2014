with Ada.Unchecked_Deallocation;

procedure Test_Move with SPARK_Mode is

   E1, E2, E3 : exception;

   type Int_Acc is access Integer;

   --  Test that exceptions are correctly handled in the borrow checker

   --  P1 should be fine, we do not exit with moved values

   procedure P1 (V : Integer; X, Y : aliased in out Int_Acc);

   procedure P1 (V : Integer; X, Y : aliased in out Int_Acc) is
   begin
      if V >= 1 then
         declare
            Tmp1 : Int_Acc := X;
         begin
            if V >= 2 then
               declare
                  Tmp2 : Int_Acc := Y;
               begin
                  if V = 3 then
                     Y := Tmp1;
                     X := Tmp2;
                     raise E1;
                  else
                     Y := Tmp2;
                  end if;
               end;
               raise E3;
            else
               X := Tmp1;
               raise E2;
            end if;
         exception
            when E3 =>
               X := Tmp1;
         end;
      end if;
   exception
      when others =>
         null;
   end P1;

   --  Incorrect versions

   procedure P2 (V : Integer; X, Y : aliased in out Int_Acc);

   procedure P2 (V : Integer; X, Y : aliased in out Int_Acc) is
   begin
      if V >= 1 then
         declare
            Tmp1 : Int_Acc := X;
         begin
            if V >= 2 then
               declare
                  Tmp2 : Int_Acc := Y;
               begin
                  if V = 3 then
                     Y := Tmp1;
                     X := Tmp2;
                     raise E1;
                  else
                     Y := Tmp2;
                  end if;
               end;
               raise E3;
            else
               X := Tmp1;
               raise E2;
            end if;
         exception
            when E3 =>
               --  Here we return from P2 with moved value for X
               null;
         end;
      end if;
   exception
      when others =>
         null;
   end P2;

   procedure P3 (V : Integer; X, Y : aliased in out Int_Acc);

   procedure P3 (V : Integer; X, Y : aliased in out Int_Acc) is
   begin
      if V >= 1 then
         declare
            Tmp1 : Int_Acc := X;
         begin
            if V >= 2 then
               declare
                  Tmp2 : Int_Acc := Y;
               begin
                  if V = 3 then
                     Y := Tmp1;
                     X := Tmp2;
                     raise E1;
                  else
                     Y := Tmp2;
                  end if;
               end;
               raise E3;
            else
               --  Here we return from P3 with moved value for X
               raise E2;
            end if;
         exception
            when E3 =>
               X := Tmp1;
         end;
      end if;
   exception
      when others =>
         null;
   end P3;

   procedure P4 (V : Integer; X, Y : aliased in out Int_Acc);

   procedure P4 (V : Integer; X, Y : aliased in out Int_Acc) is
   begin
      if V >= 1 then
         declare
            Tmp1 : Int_Acc := X;
         begin
            if V >= 2 then
               declare
                  Tmp2 : Int_Acc := Y;
               begin
                  if V = 3 then
                     Y := Tmp1;
                     X := Tmp2;
                     raise E1;
                  end if;
                  --  Here we return from P4 with moved value for Y
               end;
               raise E3;
            else
               X := Tmp1;
               raise E2;
            end if;
         exception
            when E3 =>
               X := Tmp1;
         end;
      end if;
   exception
      when others =>
         null;
   end P4;

   --  Tests with function calls

   procedure Do_Not_Raise_E1 with
     Exceptional_Cases => (E1 => False, others => True);

   procedure Do_Not_Raise_E1 is
   begin
      null;
   end Do_Not_Raise_E1;

   --  P5 should be fine, we only exit with a moved value if Do_Not_Raise_E1 raises E1

   procedure P5 (X : aliased in out Int_Acc) is
      Tmp : Int_Acc := X;
   begin
      begin
         begin
            Do_Not_Raise_E1;
            X := Tmp;
            raise E1;
         exception
            when E3 =>
               X := Tmp;
               raise E3;
         end;
      exception
         when E2 =>
            X := Tmp;
      end;
   exception
      when E1 | E2 | E3 =>
         null;
      when others =>
         X := Tmp;
   end P5;

   procedure P6 (X : aliased in out Int_Acc) is
      Tmp : Int_Acc := X;
   begin
      begin
         begin
            Do_Not_Raise_E1;
            --  Here we return from P6 with moved value for X
            raise E1;
         exception
            when E3 =>
               X := Tmp;
         end;
      exception
         when E2 =>
            X := Tmp;
      end;
   exception
      when E1 =>
         null;
      when others =>
         X := Tmp;
   end P6;

   procedure P7 (X : aliased in out Int_Acc) is
      Tmp : Int_Acc := X;
   begin
      begin
         begin
            Do_Not_Raise_E1;
            X := Tmp;
            raise E1;
         exception
            when E3 =>
               --  Here we return from P7 with moved value for X
               null;
         end;
      exception
         when E2 =>
            X := Tmp;
      end;
   exception
      when E1 =>
         null;
      when others =>
         X := Tmp;
   end P7;

   procedure P8 (X : aliased in out Int_Acc) is
      Tmp : Int_Acc := X;
   begin
      begin
         begin
            Do_Not_Raise_E1;
            X := Tmp;
            raise E1;
         exception
            when E3 =>
               X := Tmp;
         end;
      exception
         when E2 =>
            --  Here we return from P8 with moved value for X
            null;
      end;
   exception
      when E1 =>
         null;
      when others =>
         X := Tmp;
   end P8;

   procedure P9 (X : aliased in out Int_Acc) is
      Tmp : Int_Acc := X;
   begin
      begin
         begin
            Do_Not_Raise_E1;
            X := Tmp;
            raise E1;
         exception
            when E3 =>
               X := Tmp;
         end;
      exception
         when E2 =>
            X := Tmp;
      end;
   exception
      when E1 =>
         null;
      when others =>
         --  Here we return from P9 with moved value for X
         null;
   end P9;

   procedure Raise_E2 with
     No_Return,
     Exceptional_Cases => (E2 => True);

   procedure Raise_E2 is
   begin
      raise E2;
   end Raise_E2;

   --  P10 should be fine, we only exit with a moved value if Raise_E2 returns normally

   procedure P10 (X : aliased in out Int_Acc) is
      Tmp : Int_Acc := X;
   begin
      Raise_E2;
   exception
      when E2 =>
         X := Tmp;
   end P10;

begin
   null;
end;
