with Unchecked_Deallocation;

procedure Main with SPARK_Mode is
   type Int_Acc is access Integer;
   procedure Free is new Unchecked_Deallocation (Integer, Int_Acc);

   function Rand (X : Integer) return Boolean with Import;

   function F return Integer with Global => null is
      V1 : Int_Acc; --@RESOURCE_LEAK:FAIL
      V2 : Int_Acc; --@RESOURCE_LEAK:FAIL
   begin
      if Rand (0) then
         declare
            X : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
            Y : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
            Z : Int_Acc;                    --@RESOURCE_LEAK:FAIL
         begin
            return C : Integer := 13 do
               V1 := X;
               Z := Y;
               if Rand (6) then
                  return;
               end if;
               declare
                  X : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
                  Y : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
                  Z : Int_Acc;                    --@RESOURCE_LEAK:FAIL
               begin
                  V2 := X;
                  Z := Y;
                  if Rand (5) then
                     return;
                  end if;
               end;
               Free (V1);
               Free (V2);
            end return;
         end;
      end if;
      return 1;
   end;

   V1 : Int_Acc; --@RESOURCE_LEAK:FAIL
   V2 : Int_Acc; --@RESOURCE_LEAK:FAIL
   V3 : Int_Acc; --@RESOURCE_LEAK:PASS
   V4 : Int_Acc; --@RESOURCE_LEAK:PASS
begin
   if Rand (1) then
      declare
         X : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
         Y : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
         Z : Int_Acc;                    --@RESOURCE_LEAK:FAIL
      begin
         V1 := X;
         Z := Y;
         return;
      end;
   elsif Rand (2) then
      declare
         X : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
         Y : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
         Z : Int_Acc;                    --@RESOURCE_LEAK:FAIL
      begin
         V2 := X;
         Z := Y;
         goto End_All;
      end;
   elsif Rand (3) then
      for I in 1 .. 1 loop
         declare
            X : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
            Y : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
            Z : Int_Acc;                    --@RESOURCE_LEAK:FAIL
         begin
            V3 := X;
            Z := Y;
            exit when Rand (4);
         end;
      end loop;
   elsif Rand (7) then
      L: for I in 1 .. 1 loop
         declare
            X : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
            Y : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
            Z : Int_Acc;                    --@RESOURCE_LEAK:FAIL
         begin
            V3 := X;
            Z := Y;

            for I in 1 .. 1 loop
               declare
                  X : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
                  Y : Int_Acc := new Integer'(1); --@RESOURCE_LEAK:PASS
                  Z : Int_Acc;                    --@RESOURCE_LEAK:FAIL
               begin
                  V4 := X;
                  Z := Y;
                  exit L when Rand (8);
                  Free (Z);
               end;
            end loop;
            Free (Z);
         end;
      end loop L;
   end if;
   Free (V1);
   Free (V2);
   Free (V3);
   Free (V4);
   <<End_All>>
end;
