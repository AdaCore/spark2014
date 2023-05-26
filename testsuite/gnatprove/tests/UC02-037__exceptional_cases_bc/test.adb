procedure Test with SPARK_Mode is

   type Int_Acc is not null access Integer;

   E : exception;

   procedure Swap_Bad (X, Y : not null access Int_Acc; B : Boolean) with
     Exceptional_Cases => (E => True);

   procedure Swap_Bad (X, Y : not null access Int_Acc; B : Boolean) is
      Tmp : Int_Acc := X.all;
   begin
      X.all := Y.all;
      if B then
         raise E;
      end if;
      Y.all := Tmp;
   end Swap_Bad;

   procedure Swap_Bad_2 (X, Y : not null access Int_Acc; B : Boolean) with
     Exceptional_Cases => (E => True);

   procedure Swap_Bad_2 (X, Y : not null access Int_Acc; B : Boolean) is
      Tmp : Int_Acc := X.all;
   begin
      X.all := Y.all;
      Y.all := Tmp;
      if B then
         raise E;
      end if;
      Tmp := X.all;
   end Swap_Bad_2;

   procedure Raise_E (B : Boolean) with
     Exceptional_Cases => (E => True);
   procedure Raise_E (B : Boolean) is
   begin
      if B then
         raise E;
      end if;
   end Raise_E;

   procedure Swap_Call_Bad (X, Y : not null access Int_Acc; B : Boolean ) with
     Exceptional_Cases => (E => True);

   procedure Swap_Call_Bad(X, Y : not null access Int_Acc; B : Boolean) is
      Tmp : Int_Acc := X.all;
   begin
      X.all := Y.all;
      Raise_E (B);
      Y.all := Tmp;
   end Swap_Call_Bad;

   procedure Swap_Call_Bad_2 (X, Y : not null access Int_Acc; B : Boolean ) with
     Exceptional_Cases => (E => True);

   procedure Swap_Call_Bad_2 (X, Y : not null access Int_Acc; B : Boolean) is
      Tmp : Int_Acc := X.all;
   begin
      X.all := Y.all;
      Y.all := Tmp;
      Raise_E (B);
      Tmp := X.all;
   end Swap_Call_Bad_2;

   procedure Swap_OK (X, Y : not null access Int_Acc; B : Boolean) is
      Tmp : Int_Acc := X.all;
   begin
      X.all := Y.all;
      if B then
         raise E;
      end if;
      Y.all := Tmp;
   end Swap_OK;

   procedure Swap_Call_OK(X, Y : not null access Int_Acc; B : Boolean) is
      Tmp : Int_Acc := X.all;
   begin
      X.all := Y.all;
      Raise_E (B);
      Y.all := Tmp;
   end Swap_Call_OK;

begin
   null;
end;
