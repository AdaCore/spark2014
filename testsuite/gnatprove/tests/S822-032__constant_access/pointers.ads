package Pointers with SPARK_Mode is

    type Int_Acc is access Integer;
    X : constant Int_Acc := new Integer'(34);

    function Read_X return Integer with Global => X;
    procedure Change_X with Global => (In_Out => X);
    procedure Change2_X with Depends => (X => X);

end Pointers;
