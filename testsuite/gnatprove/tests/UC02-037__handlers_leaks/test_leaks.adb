with Ada.Unchecked_Deallocation;

procedure Test_Leaks with SPARK_Mode is

   E1, E2, E3 : exception;

   type Int_Acc is access Integer;
   procedure Free is new Ada.Unchecked_Deallocation (Integer, Int_Acc);

   --  Test that we check for memory leaks on scopes traversed by handled exceptions

   procedure P1 (X : Integer; Y : aliased out Integer) with
     Post => X = Y or else Y = 42;

   procedure P1 (X : Integer; Y : aliased out Integer) is
   begin
      if X >= 1 then
         declare
            X1 : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
         begin
            if X >= 2 then
               declare
                  X2 : Int_Acc := new Integer'(42); --@RESOURCE_LEAK:PASS
               begin
                  if X = 3 then
                     Y := 3;
                     Free (X2);
                     raise E1;
                  else
                     Y := X2.all;
                     Free (X2);
                  end if;
               end;
               raise E3;
            else
               Y := X1.all;
               raise E3;
            end if;
         exception
            when E3 | E1 =>
            Free (X1);
         end;
      else
         Y := X;
      end if;
   end P1;

   procedure P2 (X : Integer; Y : aliased out Integer) with
     Post => X = Y or else Y = 42;

   procedure P2 (X : Integer; Y : aliased out Integer) is
   begin
      if X >= 1 then
         declare
            X1 : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:FAIL
         begin
            if X >= 2 then
               declare
                  X2 : Int_Acc := new Integer'(42); --@RESOURCE_LEAK:PASS
               begin
                  if X = 3 then
                     Y := 3;
                     Free (X2);
                     raise E1;
                  else
                     Y := X2.all;
                     Free (X2);
                  end if;
               end;
               raise E3;
            else
               Y := X1.all;
               raise E3;
            end if;
         exception
            when E3 =>
            Free (X1);
         end;
      else
         Y := X;
      end if;
   exception
      when others =>
         null;
   end P2;

   procedure P3 (X : Integer; Y : aliased out Integer) with
     Post => X = Y or else Y = 42;

   procedure P3 (X : Integer; Y : aliased out Integer) is
   begin
      if X >= 1 then
         declare
            X1 : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:FAIL
         begin
            if X >= 2 then
               declare
                  X2 : Int_Acc := new Integer'(42); --@RESOURCE_LEAK:FAIL
               begin
                  if X = 3 then
                     Y := 3;
                     Free (X2);
                     raise E1;
                  elsif X = 4 then
                     Y := 4;
                     raise E2;
                  else
                     Y := X2.all;
                     Free (X2);
                  end if;
               end;
               raise E3;
            else
               Y := X1.all;
               raise E3;
            end if;
         exception
            when E3 | E1 =>
            Free (X1);
         end;
      else
         Y := X;
      end if;
   exception
      when others =>
         null;
   end P3;

begin
   null;
end;
