procedure Crash1 with SPARK_Mode is
    type Int_Ptr is access Integer;
    type Two_Ptrs is record
       F , G : Int_Ptr;
    end record;

    X : Two_Ptrs := (F => null, G => null);
begin
    declare
       package P is
          Y : access Integer := X.F;
       end P;
    begin
       null;
    end;
end Crash1;
