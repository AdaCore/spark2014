procedure Bad_Pointer with SPARK_Mode is
    type Int_Ptr is access Integer;
    X : Int_Ptr := new Integer'(10);
begin
   declare
      Y : Int_Ptr := X;
   begin
      Y.all := 20;
   end;
   --  incorrect, X is moved
   pragma Assert (X.all = 10);

   X := new Integer'(10);
   declare
      Y : access constant Integer := X;
   begin
      --  incorrect, X is still observed
      X.all := 10;
   end;

   X := new Integer'(10);
   declare
      Y : access constant Integer := X;
   begin
      pragma Assert (Y.all = 10);
   end;
   --  ok, X not observed anymore
   X.all := 10;

   X := new Integer'(10);
   declare
      Y : access Integer := X;
   begin
      Y.all := 20;
      --  incorrect, X is still borrowed
      pragma Assert (X.all = 10);
   end;

   X := new Integer'(10);
   declare
      Y : access Integer := X;
   begin
      Y.all := 20;
   end;
   --  ok, X not borrowed anymore
   pragma Assert (X.all = 10);


end Bad_Pointer;
