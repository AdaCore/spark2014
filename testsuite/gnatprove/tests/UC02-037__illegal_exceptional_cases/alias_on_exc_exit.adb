procedure Alias_On_Exc_Exit
  with
    SPARK_Mode => On
is

   type Int_Acc is not null access Integer;

   E : exception;

   procedure Swap (X : in out Int_Acc; Y : aliased in out Int_Acc; B : Boolean) with
     Post => not B and X.all = Y.all'Old and Y.all = X.all'Old,
     Exceptional_Cases => (E => B);

   procedure Swap (X : in out Int_Acc; Y : aliased in out Int_Acc; B : Boolean) is
      T : Int_Acc := X;
   begin
      X := Y;
      Y := T;
      if B then
         raise E;
      end if;
   end Swap;

   X : Int_Acc := new Integer'(1);
   Y : aliased Int_Acc := new Integer'(2);
begin
   Swap (X, Y, True);
exception
   when E =>
      declare
         C : constant Integer := Y.all;
      begin
         X.all := X.all + 5;
         pragma Assert (Y.all = C);  -- Does not hold at runtime
      end;
end Alias_On_Exc_Exit;
