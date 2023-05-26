with Ada.Unchecked_Deallocation;
procedure Main with SPARK_Mode is

   E1, E2, E3 : exception;

   procedure P (I : Integer; O : out Integer) with
     Post => O = I;

   procedure P (I : Integer; O : out Integer) is
   begin
      begin
         begin
            begin
               if I = 1 then
                  O := 1;
                  raise E1;
               elsif I = 2 then
                  O := 1;
                  raise E2;
               elsif I = 3 then
                  O := 1;
                  raise E3;
               else
                  O := I;
               end if;
            exception
               when E1 =>
                  null;
               when others =>
                  O := O + 1;
                  raise;
            end;
         exception
            when E1 | E3 =>
               O := O + 1;
               raise;
         end;
      exception
         when others =>
            null;
      end;
   end P;

   type Int_Acc is access Integer;

   procedure Free is new Ada.Unchecked_Deallocation (Integer, Int_Acc);

   procedure P_Leak (I : Integer; O : out Integer) with
     Post => O = I;

   procedure P_Leak (I : Integer; O : out Integer) is
      X, Y : Int_Acc := new Integer'(0);
   begin
      begin
         begin
            begin
               if I = 1 then
                  X.all := X.all + 1;
                  raise E1;
               elsif I = 2 then
                  X.all := X.all + 1;
                  raise E2;
               elsif I = 3 then
                  X.all := X.all + 1;
                  raise E3;
               else
                  X.all := I;
               end if;
               Y.all := X.all;
               Free (X);
            exception
               when E1 =>
                  Y.all := Y.all + X.all;
                  Free (X);
               when others =>
                  Y.all := X.all + 1;
                  Free (X);
                  raise;
            end;
            O := Y.all;
            Free (Y);
         exception
            when E1 | E3 =>
               Y.all := Y.all + 1;
               raise;
         end;
      exception
         when others =>
            O := Y.all;
            Free (Y);
      end;
   end P_Leak;
begin
   null;
end Main;
