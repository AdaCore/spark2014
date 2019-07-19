procedure Crash2 with SPARK_Mode is
    type Int_Ptr is access Integer;

    Z : Int_Ptr := null;
begin
    declare
       package P is
          Y : access Integer := Z;
       end P;
    begin
       null;
    end;
--    pragma Assert (X.F.all = 5);
end Crash2;
