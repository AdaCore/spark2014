procedure Walker_Bad (B : Boolean) with SPARK_Mode is
    type Int_Acc is access Integer;

    X1 : Int_Acc := new Integer'(1);
    X2 : Int_Acc := new Integer'(2);
begin
    declare
       Y : access Integer := (if B then X1 else X2);
    begin
       Y.all := 3;
    end;
    pragma Assert (if B then X1.all = 1);
end Walker_Bad;
