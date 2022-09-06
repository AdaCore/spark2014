procedure Main with SPARK_Mode is
   type Int_Acc is access Integer;

   procedure P1 (V : access Integer) is
   begin
      if V /= null then
         V.all := 0;
      end if;
   end P1;

   procedure Swap1 (V1, V2 : access Integer := null) with
     Contract_Cases =>
       (V1 /= null and V2 /= null =>
          V1.all = V2.all'Old and V2.all = V1.all'Old,
        V2 = null and V1 /= null =>
          V1.all = V1.all'Old,
        V1 = null and V2 /= null =>
          V2.all = V2.all'Old,
        others                    =>
          True)
   is
      Tmp : Integer;
   begin
      if V1 /= null and V2 /= null then
         Tmp := V1.all;
         V1.all := V2.all;
         V2.all := Tmp;
      end if;
   end Swap1;

   procedure P2 (V : Int_Acc) is
   begin
      if V /= null then
         V.all := 0;
      end if;
   end P2;

   procedure P3 (V : access Integer) with Depends => (V => V) is
   begin
      if V /= null then
         V.all := 0;
      end if;
   end P3;

   procedure P4 (V : Int_Acc) with Depends => (V => V) is
   begin
      if V /= null then
         V.all := 0;
      end if;
   end P4;

   procedure Swap2 (V1, V2 : Int_Acc := null) with
     Contract_Cases =>
       (V1 /= null and V2 /= null =>
          V1.all = V2.all'Old and V2.all = V1.all'Old,
        V2 = null and V1 /= null =>
          V1.all = V1.all'Old,
        V1 = null and V2 /= null =>
          V2.all = V2.all'Old,
        others                    =>
          True)
   is
      Tmp : Integer;
   begin
      if V1 /= null and V2 /= null then
         Tmp := V1.all;
         V1.all := V2.all;
         V2.all := Tmp;
      end if;
   end Swap2;

   V : aliased Integer := 15;
   A1 : access Integer := V'Access;
   A2 : Int_Acc := new Integer'(15); --@RESOURCE_LEAK:FAIL

begin
   P1 (null);
   Swap1;
   Swap1 (V1 => A1);
   Swap1 (V2 => A1);
   Swap1 (A1, A2);
   Swap1 (A1, A1); -- @ALIASING:CHECK
   P2 (null);
   Swap2;
   Swap2 (V1 => A2);
   Swap2 (V2 => A2);
   Swap2 (A2, A2); -- @ALIASING:CHECK
   P3 (null);
   P4 (null);
end Main;
